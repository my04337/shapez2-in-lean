-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- Gravity（落下）のユニットテスト
-- 仕様: docs/shapez2/falling.md の全例を検証する
import S2IL.Processing.Gravity

-- ============================================================
-- テストヘルパー
-- ============================================================

/-- シェイプコードから落下処理を適用し、結果のシェイプコードと比較するヘルパー -/
private def gravityTest (input expected : String) : Bool :=
    match Shape.ofString? input with
    | none => false
    | some s =>
        match s.gravity with
        | none => false
        | some result => result.toString == expected

/-- 落下しても変化しないことを検証するヘルパー -/
private def gravityNoChange (input : String) : Bool :=
    match Shape.ofString? input with
    | none => false
    | some s =>
        match s.gravity with
        | none => false
        | some result => result.toString == input

-- ============================================================
-- Quarter.canFormBond
-- ============================================================

#guard Quarter.empty.canFormBond == false
#guard Quarter.pin.canFormBond == false
#guard (Quarter.crystal .red).canFormBond == true
#guard (Quarter.crystal .green).canFormBond == true
#guard (Quarter.crystal .blue).canFormBond == true
#guard (Quarter.crystal .uncolored).canFormBond == true
#guard (Quarter.colored .circle .red).canFormBond == true
#guard (Quarter.colored .rectangle .green).canFormBond == true
#guard (Quarter.colored .star .blue).canFormBond == true
#guard (Quarter.colored .windmill .yellow).canFormBond == true

-- ============================================================
-- 構造結合 (Structural Bond)
-- ============================================================

-- 空レイヤ
private def emptyLayer : Layer := Layer.mk .empty .empty .empty .empty

-- 同レイヤ内:  隣接する結合能力あり象限は構造結合
private def structBondLayer : Layer := Layer.mk
    (.crystal .red) (.colored .rectangle .green) .empty .empty
private def structBondShape : Shape := .single structBondLayer

-- NE(crystal) と SE(colored) は隣接 → 構造結合
#guard Gravity.isStructurallyBonded structBondShape ⟨0, .ne⟩ ⟨0, .se⟩ == true
-- NE(crystal) と SW(empty) → 結合能力なし
#guard Gravity.isStructurallyBonded structBondShape ⟨0, .ne⟩ ⟨0, .sw⟩ == false
-- ピンは結合能力なし
private def pinShape : Shape := .single (Layer.mk .pin (.crystal .red) .empty .empty)
#guard Gravity.isStructurallyBonded pinShape ⟨0, .ne⟩ ⟨0, .se⟩ == false

-- 上下レイヤ間: 同方角の結合能力あり象限は構造結合（色不問）
private def crossLayerShape : Shape := .double
    (Layer.mk (.crystal .red) (.crystal .red) .empty .empty)
    (Layer.mk .empty (.colored .rectangle .green) .empty .empty)
-- L0:SE(crystal red) と L1:SE(colored green) → 垂直構造結合
#guard Gravity.isStructurallyBonded crossLayerShape ⟨0, .se⟩ ⟨1, .se⟩ == true
-- L0:NE(crystal) と L1:NE(empty) → 結合能力なし
#guard Gravity.isStructurallyBonded crossLayerShape ⟨0, .ne⟩ ⟨1, .ne⟩ == false

-- ============================================================
-- 接地 (Grounding)
-- ============================================================

-- レイヤ 0 の非空象限は接地
private def groundedL0 : Shape := .single (Layer.mk (.crystal .red) .empty .empty .empty)
#guard Gravity.isGrounded groundedL0 ⟨0, .ne⟩ == true

-- L2 の象限が L1 経由で接地しない場合
private def floatL2 : Shape := .double
    emptyLayer
    (Layer.mk (.crystal .red) .empty .empty .empty)
#guard Gravity.isGrounded floatL2 ⟨1, .ne⟩ == false

-- ピン経由の垂直接地接触（仕様 例 7 の簡易版）
private def pinGrounding : Shape := .double
    (Layer.mk (.crystal .red) .empty .empty .empty)
    (Layer.mk .pin .empty .empty .empty)
-- L1:NE(P) → L0:NE(Cr) → 垂直接地接触 → 接地
#guard Gravity.isGrounded pinGrounding ⟨1, .ne⟩ == true

-- ピンは水平接地接触を伝播しない（仕様 4.3 の例）
private def pinNoHorizontal : Shape := .double
    (Layer.mk (.crystal .red) .empty .empty .empty)
    (Layer.mk (.colored .rectangle .green) .pin .empty .empty)
-- L1:NE(Rg) → L0:NE(Cr) → 垂直接地接触 → 接地
#guard Gravity.isGrounded pinNoHorizontal ⟨1, .ne⟩ == true
-- L1:SE(P) は L0:SE が空で垂直なし、L1:NE との水平接触はピンなので不可 → 非接地
#guard Gravity.isGrounded pinNoHorizontal ⟨1, .se⟩ == false

-- ============================================================
-- 落下処理: 仕様 例 1 — 基本的な落下
-- ============================================================
-- 初期: --------:Cr------   結果: Cr------
#guard gravityTest "--------:Cr------" "Cr------"

-- ============================================================
-- 落下処理: 仕様 例 2 — 2つの独立した浮遊クラスタ
-- ============================================================
-- 初期: --------:--Cr--Cr   結果: --Cr--Cr
#guard gravityTest "--------:--Cr--Cr" "--Cr--Cr"

-- ============================================================
-- 落下処理: 仕様 例 3 — 部分浮遊（クラスタの一部が接地）
-- ============================================================
-- 初期: CrCr----:----RgRg   結果: CrCrRgRg
#guard gravityTest "CrCr----:----RgRg" "CrCrRgRg"

-- ============================================================
-- 落下処理: 仕様 例 4 — 結合による一体落下の防止
-- ============================================================
-- 初期: CrCr----:--RgRg--   結果: 変化なし
#guard gravityNoChange "CrCr----:--RgRg--"

-- ============================================================
-- 落下処理: 仕様 例 5 — 結合凍結の検証
-- ============================================================
-- 初期: Cr------:RgRg----:----Sb--
-- Sb は途中で Rg と隣接するが、結合凍結により layer 0 まで落下
-- 結果: Cr--Sb--:RgRg----
#guard gravityTest "Cr------:RgRg----:----Sb--" "Cr--Sb--:RgRg----"

-- ============================================================
-- 落下処理: 仕様 例 6 — 同列の複数落下単位
-- ============================================================
-- 初期: --------:P-------:Cr------
-- P が先に着地し、Cr は P の上に着地
-- 結果: P-------:Cr------
#guard gravityTest "--------:P-------:Cr------" "P-------:Cr------"

-- ============================================================
-- 落下処理: 仕様 例 7 — ピンを通した接地
-- ============================================================
-- 初期: CrCrCrCr:P-------:RgRgRgRg   結果: 変化なし
#guard gravityNoChange "CrCrCrCr:P-------:RgRgRgRg"

-- ============================================================
-- 落下処理: 仕様 例 8 — 切断後のピン経由接地消失
-- ============================================================
-- 初期: --CrCr--:--------:--RgRg--
-- L2 が空なので L3 の Rg は非接地 → 落下
-- 結果: --CrCr--:--RgRg--
#guard gravityTest "--CrCr--:--------:--RgRg--" "--CrCr--:--RgRg--"

-- ============================================================
-- 落下処理: 仕様 例 9 — 複数落下単位の段階的着地
-- ============================================================
-- 初期: CrCr----:--------:--RgRg--:--------:----SbSb
-- B(Rg) が先に着地し、C(Sb) は B の上に着地
-- 結果: CrCr----:--RgRg--:----SbSb
#guard gravityTest "CrCr----:--------:--RgRg--:--------:----SbSb" "CrCr----:--RgRg--:----SbSb"

-- ============================================================
-- 冪等性 (Idempotency) の検証
-- ============================================================

/-- gravity(gravity(s)) == gravity(s) を検証 -/
private def gravityIdempotent (input : String) : Bool :=
    match Shape.ofString? input with
    | none => false
    | some s =>
        match s.gravity with
        | none => true  -- 全て空の場合は冪等性成立
        | some r1 =>
            match r1.gravity with
            | none => false  -- 1回目の結果が存在するなら2回目も存在すべき
            | some r2 => r1.toString == r2.toString

#guard gravityIdempotent "--------:Cr------"
#guard gravityIdempotent "--------:--Cr--Cr"
#guard gravityIdempotent "CrCr----:----RgRg"
#guard gravityIdempotent "CrCr----:--RgRg--"
#guard gravityIdempotent "Cr------:RgRg----:----Sb--"
#guard gravityIdempotent "--------:P-------:Cr------"
#guard gravityIdempotent "CrCrCrCr:P-------:RgRgRgRg"
#guard gravityIdempotent "--CrCr--:--------:--RgRg--"
#guard gravityIdempotent "CrCr----:--------:--RgRg--:--------:----SbSb"

-- ============================================================
-- gravityOrSelf: 変化なしの場合に自身を返す
-- ============================================================

-- 落下単位がない場合
#guard (Shape.ofString? "CrCrCrCr").map Shape.gravityOrSelf
    == Shape.ofString? "CrCrCrCr"

-- 落下する場合
#guard (Shape.ofString? "--------:Cr------").map Shape.gravityOrSelf
    == Shape.ofString? "Cr------"

-- ============================================================
-- 追加テスト: エッジケース
-- ============================================================

-- 1レイヤ: 落下なし
#guard gravityNoChange "CrCrCrCr"
#guard gravityNoChange "RgRg----"

-- 全空のレイヤが混在
#guard gravityTest "--------:--------:Cr------" "Cr------"

-- ピンのみの浮遊
#guard gravityTest "--------:P-------" "P-------"

-- 複数の孤立ピンの落下
#guard gravityTest "--------:P-P-P-P-" "P-P-P-P-"
