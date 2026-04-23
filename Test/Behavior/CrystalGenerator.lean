-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- CrystalGenerator (結晶製造機) のユニットテスト
import S2IL.Operations.CrystalGenerator.CrystalGenerator

-- ============================================================
-- テストヘルパー
-- ============================================================

private def emptyLayer : Layer := Layer.mk .empty .empty .empty .empty

/-- シェイプコードから結晶製造し、結果を文字列比較するヘルパー -/
private def crystallizeTest (inputCode : String) (color : Color) (expected : String) : Bool :=
    match Shape.ofString? inputCode with
    | some s => (s.crystallize color).toString == expected
    | none => false

-- ============================================================
-- fillQuarter: 象限単位の充填
-- ============================================================

-- 空 → 結晶
#guard CrystalGenerator.fillQuarter .empty .red == Quarter.crystal .red
#guard CrystalGenerator.fillQuarter .empty .blue == Quarter.crystal .blue

-- ピン → 結晶
#guard CrystalGenerator.fillQuarter .pin .green == Quarter.crystal .green
#guard CrystalGenerator.fillQuarter .pin .uncolored == Quarter.crystal .uncolored

-- 通常パーツ → 変更なし
#guard CrystalGenerator.fillQuarter (.colored .circle .red) .blue == Quarter.colored .circle .red
#guard CrystalGenerator.fillQuarter (.colored .rectangle .green) .red == Quarter.colored .rectangle .green

-- 既存結晶 → 変更なし（別色でも上書きされない）
#guard CrystalGenerator.fillQuarter (.crystal .red) .blue == Quarter.crystal .red
#guard CrystalGenerator.fillQuarter (.crystal .green) .green == Quarter.crystal .green

-- ============================================================
-- fillLayer: レイヤ単位の充填
-- ============================================================

-- 全空レイヤ → 全結晶
#guard CrystalGenerator.fillLayer emptyLayer .red ==
    Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red)

-- 部分空レイヤ
#guard CrystalGenerator.fillLayer (Layer.mk (.colored .circle .red) .empty .empty .empty) .blue ==
    Layer.mk (.colored .circle .red) (.crystal .blue) (.crystal .blue) (.crystal .blue)

-- ピン混在レイヤ
#guard CrystalGenerator.fillLayer (Layer.mk .pin .pin .empty .empty) .green ==
    Layer.mk (.crystal .green) (.crystal .green) (.crystal .green) (.crystal .green)

-- 全非空レイヤ → 変更なし
#guard CrystalGenerator.fillLayer
    (Layer.mk (.colored .circle .red) (.colored .rectangle .green)
              (.colored .star .blue) (.colored .windmill .uncolored)) .red ==
    Layer.mk (.colored .circle .red) (.colored .rectangle .green)
             (.colored .star .blue) (.colored .windmill .uncolored)

-- ============================================================
-- 基本テスト: 1レイヤシェイプ
-- ============================================================

-- 全空 → 全結晶（ofString? では全空はパースできないので直接構築）
#guard (Shape.single emptyLayer).crystallize .red ==
    Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red))

-- 部分空 → 空のみ結晶化
-- CrRg---- + 赤液剤 → CrRgcrcr
#guard crystallizeTest "CrRg----" .red "CrRgcrcr"

-- 全非空 → 変更なし
#guard crystallizeTest "CrRgSbWu" .red "CrRgSbWu"

-- 1象限のみ空
#guard crystallizeTest "CrRgSb--" .blue "CrRgSbcb"

-- ============================================================
-- ピンの充填
-- ============================================================

-- 全ピン → 全結晶
#guard crystallizeTest "P-P-P-P-" .blue "cbcbcbcb"

-- ピンと空の混在
#guard crystallizeTest "P---P---" .green "cgcgcgcg"

-- ピンと通常パーツの混在
#guard crystallizeTest "P-Cr--Rg" .yellow "cyCrcyRg"

-- ============================================================
-- 既存結晶は上書きされない
-- ============================================================

-- 全結晶（赤）に青液剤 → 変更なし
#guard crystallizeTest "crcrcrcr" .blue "crcrcrcr"

-- 結晶と空の混在 → 空のみ充填、既存結晶は維持
#guard crystallizeTest "crcr----" .blue "crcrcbcb"

-- 異色結晶の混在 → 全て維持
#guard crystallizeTest "crcgcbcy" .red "crcgcbcy"

-- ============================================================
-- 複数レイヤ（全レイヤに適用される）
-- ============================================================

-- 2レイヤ: 両方に空がある
#guard crystallizeTest "CrRg----:----SbWu" .red "CrRgcrcr:crcrSbWu"

-- 2レイヤ: ピンを含む
#guard crystallizeTest "P-P-----:CrRg----" .green "cgcgcgcg:CrRgcgcg"

-- 3レイヤ
#guard crystallizeTest "Cr------:--Rg----:----Sb--" .uncolored "Crcucucu:cuRgcucu:cucuSbcu"

-- 4レイヤ: 全非空 → 変更なし
#guard crystallizeTest "CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu" .red
    "CrCrCrCr:RgRgRgRg:SbSbSbSb:WuWuWuWu"

-- ============================================================
-- 異なる色の液剤（直接構築で全色テスト）
-- ============================================================

#guard (Shape.single emptyLayer).crystallize .red ==
    Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red))
#guard (Shape.single emptyLayer).crystallize .green ==
    Shape.single (Layer.mk (.crystal .green) (.crystal .green) (.crystal .green) (.crystal .green))
#guard (Shape.single emptyLayer).crystallize .blue ==
    Shape.single (Layer.mk (.crystal .blue) (.crystal .blue) (.crystal .blue) (.crystal .blue))
#guard (Shape.single emptyLayer).crystallize .yellow ==
    Shape.single (Layer.mk (.crystal .yellow) (.crystal .yellow) (.crystal .yellow) (.crystal .yellow))
#guard (Shape.single emptyLayer).crystallize .cyan ==
    Shape.single (Layer.mk (.crystal .cyan) (.crystal .cyan) (.crystal .cyan) (.crystal .cyan))
#guard (Shape.single emptyLayer).crystallize .magenta ==
    Shape.single (Layer.mk (.crystal .magenta) (.crystal .magenta) (.crystal .magenta) (.crystal .magenta))
#guard (Shape.single emptyLayer).crystallize .white ==
    Shape.single (Layer.mk (.crystal .white) (.crystal .white) (.crystal .white) (.crystal .white))
#guard (Shape.single emptyLayer).crystallize .uncolored ==
    Shape.single (Layer.mk (.crystal .uncolored) (.crystal .uncolored) (.crystal .uncolored) (.crystal .uncolored))

-- ============================================================
-- 連続適用（異なる色の結晶を組み合わせ）
-- ============================================================

-- 1回目: 赤で部分充填 → 2回目: 青で残りを充填
-- Cr------ に赤液剤 → Crcrcrcr → 既に全非空なので青液剤 → 変化なし
private def twoPass : Shape :=
    match Shape.ofString? "Cr------" with
    | some s => (s.crystallize .red).crystallize .blue
    | none => Shape.single emptyLayer

#guard twoPass.toString == "Crcrcrcr"

-- Cr--Rg-- に赤液剤 → CrcrRgcr → 全非空なので青液剤 → 変化なし
private def twoPass2 : Shape :=
    match Shape.ofString? "Cr--Rg--" with
    | some s => (s.crystallize .red).crystallize .blue
    | none => Shape.single emptyLayer

#guard twoPass2.toString == "CrcrRgcr"
