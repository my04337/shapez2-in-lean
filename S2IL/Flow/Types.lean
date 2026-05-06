-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Types

/-!
# S2IL.Flow.Types

Shape Processing Flow の基礎型定義。

| 型 | 概要 |
|---|---|
| `FlowAmount` | Flow 上で扱う抽象量 |
| `StreamKind` | ベルト / パイプのストリーム種別 |
| `Fluid` | 色と量を持つ液剤 |
| `PortSpec` | 接続ポートが受け付けるストリーム種別と名前 |
| `NodeId` / `PortId` | 後続の FlowGraph / port lookup 用の識別子 |
-/

namespace S2IL

/-- Flow 評価や処理能力解析で扱う抽象量。

実ゲーム上の単位（個/分、L/分、tick あたり量）は後続の設定層で解釈する。 -/
structure FlowAmount where
  /-- 単位解釈前の非負の量。 -/
  units : Nat
deriving Repr, DecidableEq, BEq

/-- 加工ライン上を流れるストリームの種別。 -/
inductive StreamKind where
  | belt
  | pipe
deriving Repr, DecidableEq, BEq

/-- パイプ上を流れる液剤。色と抽象量を持つ。 -/
structure Fluid where
  /-- 液剤の色。 -/
  color : Color
  /-- 液剤の抽象量。 -/
  amount : FlowAmount
deriving Repr, DecidableEq, BEq

/-- マシンの入出力ポート仕様。 -/
structure PortSpec where
  /-- このポートが受け付けるストリーム種別。 -/
  kind : StreamKind
  /-- 設計上のポート名。 -/
  name : String
deriving Repr, DecidableEq, BEq

/-- FlowGraph 内のマシンノードを参照する識別子。 -/
abbrev NodeId := Nat

/-- `MachineSpec` 内のポートを参照する識別子。 -/
abbrev PortId := Nat

end S2IL
