-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Wires.Signal
import S2IL.Wires.Gates
import S2IL.Wires.Elements

/-!
# S2IL.Wires facade

ワイヤー系 (Layer A-3) のスケルトン。Phase B では `WireSignal` 型のみ scaffold。

## 公開 API

- `WireSignal` と基本コンストラクタ（off / boolean / shape / color）

## サブモジュール（公開）

- `S2IL.Wires.Signal`    — A-3-1
- `S2IL.Wires.Gates`     — A-3-2
- `S2IL.Wires.Elements`  — A-3-3 / A-3-4

## Internal（外部 import 禁止）

- `S2IL.Wires.Internal.*` （Phase C で整備）
-/
