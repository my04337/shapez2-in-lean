-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- BFS: 汎用 BFS 定義・帰納法テンプレート
import S2IL.Kernel.BFS.GenericBfs

-- Transform: 回転・対称性変換の補題群
import S2IL.Kernel.Transform.Rotate
import S2IL.Kernel.Transform.Rotate180Lemmas

-- Bond: 結合判定・クラスタ計算
import S2IL.Kernel.Bond.CrystalBond

/-!
# Kernel: 共通理論（Gravity 非依存の横断基盤）

BFS・Bond・Transform の 3 サブモジュールを集約する re-export ハブ。
加工操作（Operations）から共通基盤に到達するためのエントリポイント。
-/
