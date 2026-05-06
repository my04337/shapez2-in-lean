-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow.Types

/-!
# S2IL.Flow.Capability

Shape Processing Flow の抽象処理能力。

基本スループット値や容量値のプリセットはここに置かず、後続の設定層から
`Throughput` / `Capacity` の値として差し込む。

| 型 | 概要 |
|---|---|
| `Throughput` | 単位時間あたりの処理量 |
| `Capacity` | 入出力や内部待ちの抽象容量 |
| `ThroughputRequirement` | 加工ラインが満たすべきスループット要求 |
| `Capability` | マシンまたは加工ラインが提供する処理能力 |
-/

namespace S2IL

/-- 単位時間あたりに処理・搬送できる抽象量。 -/
structure Throughput where
  /-- 対象となるストリーム種別。 -/
  kind : StreamKind
  /-- 単位時間あたりの抽象量。 -/
  amount : FlowAmount
deriving Repr, DecidableEq, BEq

/-- 入出力や内部待ちで保持できる抽象容量。 -/
structure Capacity where
  /-- 対象となるストリーム種別。 -/
  kind : StreamKind
  /-- 保持できる抽象量。 -/
  amount : FlowAmount
deriving Repr, DecidableEq, BEq

/-- 加工ラインやマシンに対するスループット要求。 -/
structure ThroughputRequirement where
  /-- 要求されるストリームごとの処理量。 -/
  targets : List Throughput
deriving Repr, DecidableEq, BEq

/-- マシンまたは加工ラインが提供する抽象処理能力。 -/
structure Capability where
  /-- 主出力として観測する基準スループット。 -/
  throughput : Throughput
  /-- 入力側の抽象容量。 -/
  inputCapacity : Capacity
  /-- 出力側の抽象容量。 -/
  outputCapacity : Capacity
  /-- 稼働に必要な供給スループット。 -/
  requires : List Throughput
  /-- 稼働時に消費するスループット。 -/
  consumes : List Throughput
  /-- 稼働時に産出する副次的なスループット。 -/
  produces : List Throughput
deriving Repr, DecidableEq, BEq

end S2IL
