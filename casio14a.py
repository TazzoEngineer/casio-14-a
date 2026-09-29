#!/usr/bin/env python3
"""
CASIO 14-A リレー式計算機 ターミナル再現 (curses / 依存ライブラリなし)

仕様: 加減置数14桁, 積14桁, 商12桁, 四則演算14桁, 定数記憶5桁×3組, リレー341個

注意: 実機の内部構成(リレーの物理配置・1桁の符号化方式)と操作盤のキー配置は
公開資料で確認できなかったため、ここでは推定で再構成している。
  - 各レジスタは1桁あたりBCD(8-4-2-1)4個のリレーで保持
  - 総数が実機と同じ341個になるよう、制御リレーを配分
  - 操作盤のキー配置は KEYPAD で定義(仮)。実機に合わせる場合はここを書き換える

実行: python3 casio14a.py        テスト: python3 casio14a.py --test
"""
import curses
import locale
import os
import sys
import time
import unicodedata
from collections import deque

N = 14            # 置数・累算・積 14桁
QUOT_SIG = 12     # 商 12桁
KDIGITS = 5       # 定数記憶 5桁
KSETS = 3         # 定数記憶 3組
BITS = (8, 4, 2, 1)

ON, OFF = "■", "□"

# 操作盤のキー配置 (仮)。(表示ラベル, 内部キー)
KEYPAD = [
    [("定1", "K1"), ("定2", "K2"), ("定3", "K3"), ("記", "M")],
    [("7", "7"), ("8", "8"), ("9", "9"), ("÷", "/")],
    [("4", "4"), ("5", "5"), ("6", "6"), ("×", "*")],
    [("1", "1"), ("2", "2"), ("3", "3"), ("－", "-")],
    [("C", "C"), ("0", "0"), ("＝", "="), ("＋", "+")],
]

# 端末のキー → 内部キー
KEYMAP = {str(i): str(i) for i in range(10)}
KEYMAP.update({
    "+": "+", "-": "-", "*": "*", "x": "*", "X": "*", "/": "/",
    "=": "=", "\n": "=", "\r": "=",
    "c": "C", "C": "C", "\x1b": "C", "\x7f": "C", "\b": "C",
    "m": "M", "M": "M", "a": "K1", "s": "K2", "d": "K3",
})

# 速度: (1ステップの待ち秒, 何ステップごとに描画するか)
SPEEDS = [(0.05, 1), (0.015, 1), (0.003, 1), (0.001, 5), (0.0, 60)]
DEFAULT_SPEED = 2

OPS = "+-*/"
SEQS = "転加減移補"   # 転送 加算 減算 桁移し 補数
KEY_RELAYS = "0123456789+-*/=C"


class Reg:
    def __init__(self, n=N):
        self.n = n
        self.d = [0] * n    # d[0] が最下位桁
        self.neg = False
        self.scale = 0      # 小数点以下の桁数

    def zero(self):
        self.d = [0] * self.n
        self.neg = False
        self.scale = 0

    def is_zero(self):
        return not any(self.d)

    def sig(self):
        for i in range(self.n - 1, -1, -1):
            if self.d[i]:
                return i + 1
        return 0

    def text(self):
        s = "".join(str(x) for x in reversed(self.d)).lstrip("0")
        s = s.rjust(self.scale + 1, "0")
        if self.scale:
            s = s[:-self.scale] + "." + s[-self.scale:]
        return ("-" if self.neg and not self.is_zero() else "") + s


class Machine:
    """リレー計算機本体。演算はジェネレータで1ステップずつ進む(yield = リレー動作1回)。"""

    def __init__(self):
        self.R, self.A, self.B, self.Q = Reg(), Reg(), Reg(), Reg()
        self.K = [Reg(KDIGITS) for _ in range(KSETS)]
        self.pending = None      # 保留中の演算
        self.active_op = None    # 実行中の演算
        self.eq_active = False
        self.entered = False     # 置数中か
        self.show = "A"          # 表示するレジスタ
        self.error = False
        self.store_mode = False
        self.pos = None          # 桁送りリレー
        self.carry = 0
        self.sumd = None
        self.seq = None
        self.count = 0
        self.key = None
        self.key_t = 0.0
        self.msg = ""
        self.flips = 0
        self._snap = self.snapshot()

    # ---- リレー群 ----
    def relay_groups(self):
        g = []
        for name in "RABQ":
            reg = getattr(self, name)
            g.append((name, [bool(reg.d[i] & w) for i in range(N) for w in BITS]))
        for k, reg in enumerate(self.K):
            g.append((f"K{k+1}", [bool(reg.d[i] & w) for i in range(KDIGITS) for w in BITS]))
        g.append(("ring", [self.pos == i for i in range(N)]))
        g.append(("carry", [bool(self.carry)]))
        s = self.sumd or 0
        g.append(("sum", [bool(s & w) for w in BITS]))
        op = self.active_op or self.pending
        g.append(("op", [op == o for o in OPS] + [self.eq_active]))
        g.append(("seq", [self.seq == s for s in SEQS]))
        g.append(("count", [bool(self.count & w) for w in BITS]))
        g.append(("scale", [bool(self.A.scale & w) for w in BITS]))
        g.append(("sign", [self.R.neg, self.A.neg, self.B.neg, self.Q.neg]))
        g.append(("key", [self.key == k for k in KEY_RELAYS]))
        return g

    def snapshot(self):
        return [b for _, lst in self.relay_groups() for b in lst]

    def after_step(self):
        snap = self.snapshot()
        self.flips += sum(a != b for a, b in zip(snap, self._snap))
        self._snap = snap

    def idle(self):
        self.pos = None
        self.carry = 0
        self.sumd = None
        self.seq = None
        self.count = 0
        self.active_op = None
        self.eq_active = False

    def fail(self, msg):
        self.error = True
        self.msg = msg
        self.pending = None
        self.show = "A"

    # ---- キー入力 ----
    def press(self, k):
        self.key = k
        self.key_t = time.monotonic()
        if k == "C":
            yield from self.clear_all()
            return
        if self.error:
            return
        self.msg = ""
        try:
            if k.isdigit():
                yield from self.digit(int(k))
            elif k in OPS:
                yield from self.operator(k)
            elif k == "=":
                yield from self.equals()
            elif k == "M":
                self.store_mode = not self.store_mode
            elif k in ("K1", "K2", "K3"):
                yield from self.constant(int(k[1]) - 1)
        finally:
            self.idle()

    def clear_all(self):
        self.seq = "転"
        for i in range(N):
            for reg in (self.R, self.A, self.B, self.Q):
                reg.d[i] = 0
            self.pos = i
            yield
        for reg in (self.R, self.A, self.B, self.Q):
            reg.zero()
        self.pending = None
        self.entered = False
        self.show = "A"
        self.error = False
        self.store_mode = False
        self.msg = ""
        self.idle()

    def digit(self, v):
        if not self.entered:
            self.R.zero()
            self.entered = True
            self.show = "R"
        if self.R.d[N - 1]:
            self.msg = "置数は14桁まで"
            return
        if self.R.is_zero() and v == 0:
            return
        self.seq = "移"
        self.R.d = [v] + self.R.d[:-1]
        yield

    def operator(self, op):
        if self.pending and self.entered:
            yield from self.execute(self.pending)
        elif self.pending is None and self.entered:
            yield from self.load_A()
        if self.error:
            return
        self.pending = op
        self.entered = False
        self.show = "A"

    def equals(self):
        self.eq_active = True
        if self.pending and self.entered:
            yield from self.execute(self.pending)
        elif self.pending is None and self.entered:
            yield from self.load_A()
        if not self.error:
            self.pending = None
        self.entered = False
        self.show = "A"

    def constant(self, idx):
        K = self.K[idx]
        if self.store_mode:
            self.store_mode = False
            src = self.R if self.show == "R" else self.A
            if src.scale or src.neg or src.sig() > KDIGITS:
                self.msg = "定数は5桁以内の正の整数のみ"
                return
            self.seq = "転"
            for i in range(KDIGITS):
                K.d[i] = src.d[i]
                self.pos = i
                yield
            self.msg = f"定数{idx + 1}に記憶"
            self.entered = False
        else:
            self.R.zero()
            self.seq = "転"
            for i in range(KDIGITS):
                self.R.d[i] = K.d[i]
                self.pos = i
                yield
            self.entered = True
            self.show = "R"

    # ---- 基本動作 ----
    def transfer(self, src, dst, shift=0):
        """src を shift 桁ずらして dst へ転送。あふれたら True を返す。"""
        self.seq = "転"
        over = any(src.d[j] for j in range(N - shift, N))
        for i in range(N):
            j = i - shift
            dst.d[i] = src.d[j] if j >= 0 else 0
            self.pos = i
            yield
        return over

    def load_A(self):
        yield from self.transfer(self.R, self.A)
        self.A.neg = self.R.neg
        self.A.scale = 0

    def serial(self, dst, src, offset=0, sub=False):
        """1桁ずつ加算(減算)。(最上位からの桁上げ/借り, 桁あふれ) を返す。"""
        self.seq = "減" if sub else "加"
        over = any(src.d[j] for j in range(N - offset, N))
        carry = 0
        for i in range(offset, N):
            s = src.d[i - offset]
            if sub:
                v = dst.d[i] - s - carry
                carry = 1 if v < 0 else 0
            else:
                v = dst.d[i] + s + carry
                carry = v // 10
            v %= 10
            dst.d[i] = v
            self.pos, self.carry, self.sumd = i, carry, v
            yield
        return carry, over

    def complement(self, dst):
        """dst = 10^N - dst (減算で負になったときの補数化)"""
        self.seq = "補"
        borrow = 0
        for i in range(N):
            v = -dst.d[i] - borrow
            borrow = 1 if v < 0 else 0
            v %= 10
            dst.d[i] = v
            self.pos, self.carry, self.sumd = i, borrow, v
            yield

    def clear_reg(self, reg):
        self.seq = "転"
        reg.zero()
        yield

    def normalize(self):
        A = self.A
        self.seq = "移"
        while A.scale > 0 and A.d[0] == 0:
            A.d = A.d[1:] + [0]
            A.scale -= 1
            yield
        if A.is_zero():
            A.neg = False
            A.scale = 0

    # ---- 四則演算 ----
    def execute(self, op):
        self.active_op = op
        A, R, B, Q = self.A, self.R, self.B, self.Q
        if op in "+-":
            if (yield from self.transfer(R, B, A.scale)):
                return self.fail("桁あふれ")
            B.neg = R.neg ^ (op == "-")
            if A.neg == B.neg:
                carry, over = yield from self.serial(A, B)
                if carry or over:
                    return self.fail("桁あふれ")
            else:
                borrow, _ = yield from self.serial(A, B, sub=True)
                if borrow:
                    yield from self.complement(A)
                    A.neg = not A.neg

        elif op == "*":
            sign, scale = A.neg ^ R.neg, A.scale
            yield from self.transfer(A, B)
            B.neg = A.neg
            yield from self.transfer(R, Q)
            Q.neg = R.neg
            yield from self.clear_reg(A)
            A.scale = scale
            for i in range(N):
                while Q.d[i] > 0:
                    self.count = Q.d[i]
                    carry, over = yield from self.serial(A, B, i)
                    if carry or over:
                        return self.fail("桁あふれ")
                    Q.d[i] -= 1
                    self.count = Q.d[i]
            A.neg = sign

        elif op == "/":
            if R.is_zero():
                return self.fail("0では割れません")
            if R.d[N - 1]:
                return self.fail("除数は13桁まで")
            sign, sa = A.neg ^ R.neg, A.scale
            yield from self.transfer(R, B)
            B.neg = R.neg
            yield from self.transfer(A, Q)
            Q.neg = A.neg
            yield from self.clear_reg(A)
            shifts = decimals = 0
            while True:
                if shifts >= N and (A.is_zero() or Q.d[N - 1] or Q.sig() >= QUOT_SIG
                                    or sa + decimals >= N - 1):
                    break
                # 累算A と 乗除Q をひと続きにして左へ1桁送る
                self.seq = "移"
                A.d = [Q.d[N - 1]] + A.d[:-1]
                Q.d = [0] + Q.d[:-1]
                yield
                if shifts >= N:
                    decimals += 1
                shifts += 1
                q = 0
                while True:
                    self.count = q
                    borrow, _ = yield from self.serial(A, B, sub=True)
                    if borrow:
                        yield from self.serial(A, B)   # 引きすぎを戻す
                        break
                    q += 1
                Q.d[0] = q
                yield
            yield from self.transfer(Q, A)
            A.scale = sa + decimals
            A.neg = sign

        yield from self.normalize()


# ---------------------------------------------------------------- 画面

def dwidth(s):
    return sum(2 if unicodedata.east_asian_width(c) in "WF" else 1 for c in s)


X0 = 2
LX = X0 + 9            # 桁の列の左端
RX = LX + N * 3 + 4    # 右カラム
RW = 40                # 右カラムの枠幅
MIN_H, MIN_W = 42, RX + RW + 1


class UI:
    def __init__(self, scr, m):
        self.scr, self.m = scr, m
        curses.start_color()
        curses.use_default_colors()
        c256 = curses.COLORS >= 256
        pairs = {
            1: (214 if c256 else curses.COLOR_YELLOW, -1),   # 点灯ランプ
            2: (237 if c256 else curses.COLOR_BLACK, -1),    # 消灯ランプ
            3: (203 if c256 else curses.COLOR_RED, -1),      # リレー動作
            4: (240 if c256 else curses.COLOR_WHITE, -1),    # リレー復旧
            5: (67 if c256 else curses.COLOR_CYAN, -1),      # 枠
            6: (0, 214 if c256 else curses.COLOR_YELLOW),    # 押下キー
            7: (196 if c256 else curses.COLOR_RED, -1),      # エラー
            8: (250 if c256 else curses.COLOR_WHITE, -1),    # ラベル
        }
        for n, (fg, bg) in pairs.items():
            curses.init_pair(n, fg, bg)
        P = curses.color_pair
        self.LAMP = P(1) | curses.A_BOLD
        self.DARK = P(2)
        self.RON = P(3) | curses.A_BOLD
        self.ROFF = P(4)
        self.FRAME = P(5)
        self.KEYP = P(6) | curses.A_BOLD
        self.ERR = P(7) | curses.A_BOLD
        self.LABEL = P(8)

    def put(self, y, x, s, attr=0):
        try:
            self.scr.addstr(y, x, s, attr)
        except curses.error:
            pass

    def relay(self, y, x, on):
        self.put(y, x, ON if on else OFF, self.RON if on else self.ROFF)

    def box(self, y, x, h, w, title):
        s, a = self.scr, self.FRAME
        try:
            s.attron(a)
            s.hline(y, x + 1, curses.ACS_HLINE, w - 2)
            s.hline(y + h - 1, x + 1, curses.ACS_HLINE, w - 2)
            s.vline(y + 1, x, curses.ACS_VLINE, h - 2)
            s.vline(y + 1, x + w - 1, curses.ACS_VLINE, h - 2)
            s.addch(y, x, curses.ACS_ULCORNER)
            s.addch(y, x + w - 1, curses.ACS_URCORNER)
            s.addch(y + h - 1, x, curses.ACS_LLCORNER)
            s.addch(y + h - 1, x + w - 1, curses.ACS_LRCORNER)
        except curses.error:
            pass
        finally:
            s.attroff(a)
        self.put(y, x + 2, f" {title} ", self.FRAME | curses.A_BOLD)

    def draw(self, busy, speed):
        m, scr = self.m, self.scr
        scr.erase()
        h, w = scr.getmaxyx()
        if h < MIN_H or w < MIN_W:
            self.put(0, 0, f"端末を {MIN_W}x{MIN_H} 以上に広げてください (現在 {w}x{h})")
            scr.refresh()
            return
        self.put(0, X0, "CASIO 14-A  リレー式計算機", self.LAMP)
        self.put(0, X0 + 30, "加減置数14桁 積14桁 商12桁 定数記憶5桁×3組", self.LABEL)

        # ---- 表示部 (豆ランプ: 各桁 0〜9 を縦に並べ、該当数字だけ点灯)
        self.box(2, X0 - 1, 13, LX + N * 3 - X0 + 3, "表示")
        reg = m.R if m.show == "R" else m.A
        width = max(reg.sig(), reg.scale + 1)
        for c in range(N):
            i = N - 1 - c
            x = LX + c * 3 + 1
            shown = i < width
            for v in range(10):
                lit = shown and reg.d[i] == v
                self.put(3 + v, x, str(v), self.LAMP if lit else self.DARK)
            self.put(13, x + 1, ".", self.LAMP if (reg.scale and i == reg.scale) else self.DARK)
        neg = reg.neg and not reg.is_zero()
        self.put(6, X0 + 1, "負", self.LAMP if neg else self.DARK)
        self.put(9, X0 + 1, "誤", self.ERR if m.error else self.DARK)

        # ---- リレー架
        self.put(16, X0, "桁送り", self.LABEL)
        for c in range(N):
            self.relay(16, LX + c * 3 + 1, m.pos == N - 1 - c)
        regs = [("置数 R", m.R), ("累算 A", m.A), ("被数 B", m.B), ("乗除 Q", m.Q)]
        for r, (label, rg) in enumerate(regs):
            base = 18 + r * 5
            self.put(base, X0, label, self.LABEL)
            for b, wt in enumerate(BITS):
                self.put(base + b, LX - 1, str(wt), self.DARK)
                for c in range(N):
                    self.relay(base + b, LX + c * 3 + 1, rg.d[N - 1 - c] & wt)
        self.put(37, X0, "定数記憶", self.LABEL)
        for k, rg in enumerate(m.K):
            bx = LX + k * 16
            self.put(37, bx, f"定数{k + 1}", self.LABEL)
            for b, wt in enumerate(BITS):
                if k == 0:
                    self.put(38 + b, LX - 1, str(wt), self.DARK)
                for c in range(KDIGITS):
                    self.relay(38 + b, bx + c * 2, rg.d[KDIGITS - 1 - c] & wt)

        # ---- 操作盤
        self.box(2, RX, 13, RW, "操作盤 (配置は仮)")
        for r, row in enumerate(KEYPAD):
            for c, key in enumerate(row):
                if key is None:
                    continue
                label, kid = key
                pad = 3 - dwidth(label)
                text = "[" + " " * (pad // 2) + label + " " * (pad - pad // 2) + "]"
                pressed = m.key == kid or (kid == "M" and m.store_mode)
                self.put(4 + r * 2, RX + 5 + c * 8, text, self.KEYP if pressed else self.LABEL)

        # ---- 制御リレー
        self.box(16, RX, 10, RW, "制御リレー")

        def row(y, label, items):
            """items: 文字列はラベル、それ以外はリレー1個"""
            self.put(y, RX + 2, label, self.LABEL)
            x = RX + 8
            for it in items:
                if isinstance(it, str):
                    self.put(y, x, it, self.DARK)
                    x += dwidth(it)
                else:
                    self.relay(y, x, it)
                    x += 1

        def named(pairs):
            out = []
            for name, on in pairs:
                out += [name, on, " "]
            return out

        op = m.active_op or m.pending
        s = m.sumd or 0
        row(17, "桁上", [m.carry, "   和 "] + [s & wt for wt in BITS])
        row(18, "指令", named([(n, op == o) for n, o in zip("加減乗除", OPS)] + [("等", m.eq_active)]))
        row(19, "順序", named([(n, m.seq == n) for n in SEQS]))
        row(20, "計数", [m.count & wt for wt in BITS] + [" 小数 "] + [m.A.scale & wt for wt in BITS])
        row(21, "符号", named([(n, getattr(m, n).neg) for n in "RABQ"]))
        row(22, "鍵", named([(k, m.key == k) for k in "0123456789"]))
        row(23, "", named([(n, m.key == k) for n, k in zip("加減乗除等消", "+-*/=C")]))

        total = len(m.snapshot())
        self.put(27, RX, f"リレー総数 {total}個 (配置は推定)", self.LABEL)
        self.put(28, RX, f"動作回数   {m.flips:,}", self.LABEL)
        self.put(29, RX, f"速度       {speed + 1} / {len(SPEEDS)}", self.LABEL)
        self.put(30, RX, "状態       " + ("演算中…" if busy else "待機"),
                 self.LAMP if busy else self.LABEL)
        if m.store_mode:
            self.put(31, RX, "記憶モード: a/s/d で定数へ格納", self.LAMP)
        if m.msg:
            self.put(32, RX, m.msg, self.ERR if m.error else self.LAMP)

        help_lines = [
            "0-9       置数",
            "+ - * /   加 減 乗 除  (x も乗)",
            "= Enter   等",
            "c Esc BS  消去",
            "a s d     定数1〜3 呼出",
            "m → a/s/d 定数へ記憶",
            "[ ]       速度 遅く/速く",
            "q         終了",
        ]
        for i, line in enumerate(help_lines):
            self.put(34 + i, RX, line, self.DARK if i % 2 else self.LABEL)
        scr.refresh()


def run(scr):
    curses.curs_set(0)
    scr.nodelay(True)
    m = Machine()
    ui = UI(scr, m)
    queue = deque()
    job = None
    speed = DEFAULT_SPEED
    while True:
        while True:
            try:
                ch = scr.get_wch()
            except curses.error:
                break
            if ch in ("q", "Q"):
                return
            if ch == "[":
                speed = max(0, speed - 1)
            elif ch == "]":
                speed = min(len(SPEEDS) - 1, speed + 1)
            elif isinstance(ch, str) and ch in KEYMAP:
                queue.append(KEYMAP[ch])
            elif ch == curses.KEY_RESIZE:
                scr.clear()

        if job is None and queue:
            job = m.press(queue.popleft())
        if job is not None:
            delay, every = SPEEDS[speed]
            try:
                for _ in range(every):
                    next(job)
                    m.after_step()
            except StopIteration:
                job = None
                m.after_step()
            ui.draw(job is not None, speed)
            if delay:
                time.sleep(delay)
        else:
            if m.key and time.monotonic() - m.key_t > 0.15:
                m.key = None
                m.after_step()
            ui.draw(False, speed)
            time.sleep(0.02)


# ---------------------------------------------------------------- テスト

def calc(keys):
    m = Machine()
    for k in keys:
        for _ in m.press(KEYMAP.get(k, k)):
            pass
    return "E" if m.error else (m.R if m.show == "R" else m.A).text()


def selftest():
    cases = [
        ("12+3=", "15"),
        ("5-8=", "-3"),
        ("-5=", "-5"),
        ("1234567*7654321=", str(1234567 * 7654321)),
        ("12345678*12345678=", "E"),          # 積15桁 → あふれ
        ("99999999999999+1=", "E"),
        ("10/3=", "3.33333333333"),
        ("1/3=", "0.333333333333"),
        ("1/8=", "0.125"),
        ("10/2=", "5"),
        ("7/0=", "E"),
        ("3/2+1=", "2.5"),
        ("3/2*4=", "6"),
        ("2/3*3=", "1.999999999998"),
        ("5-2*3=", "9"),                     # 逐次計算
        ("0-6/4=", "-1.5"),
        ("12+3+4-1=", "18"),
        ("123", "123"),
        ("99999999999999/7=", str(99999999999999 // 7)),
        ("5ma8+a=", "13"),                    # 定数記憶
    ]
    ok = True
    for keys, want in cases:
        got = calc(keys)
        mark = "OK " if got == want else "NG "
        ok &= got == want
        print(f"{mark} {keys:<22} -> {got:<18} (期待 {want})")
    print("relays:", len(Machine().snapshot()))
    return ok


if __name__ == "__main__":
    if "--test" in sys.argv:
        sys.exit(0 if selftest() else 1)
    locale.setlocale(locale.LC_ALL, "")
    os.environ.setdefault("ESCDELAY", "25")
    curses.wrapper(run)
