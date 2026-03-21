-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

-- CrystalBond (結晶結合) と Shatter (砕け散り) のユニットテスト
import S2IL.Behavior.Shatter

-- ============================================================
-- テスト用データ
-- ============================================================

-- 空レイヤ
private def emptyLayer : Layer := Layer.mk .empty .empty .empty .empty

-- ============================================================
-- Quarter.isFragile
-- ============================================================

#guard Quarter.empty.isFragile == false
#guard Quarter.pin.isFragile == false
#guard (Quarter.colored .circle .red).isFragile == false
#guard (Quarter.colored .rectangle .green).isFragile == false
#guard (Quarter.crystal .red).isFragile == true
#guard (Quarter.crystal .green).isFragile == true
#guard (Quarter.crystal .blue).isFragile == true
#guard (Quarter.crystal .uncolored).isFragile == true

-- ============================================================
-- Direction.adjacent
-- ============================================================

-- 隣接ペア
#guard Direction.ne.adjacent .se == true
#guard Direction.se.adjacent .ne == true
#guard Direction.se.adjacent .sw == true
#guard Direction.sw.adjacent .se == true
#guard Direction.sw.adjacent .nw == true
#guard Direction.nw.adjacent .sw == true
#guard Direction.nw.adjacent .ne == true
#guard Direction.ne.adjacent .nw == true

-- 対角は隣接しない
#guard Direction.ne.adjacent .sw == false
#guard Direction.se.adjacent .nw == false
#guard Direction.sw.adjacent .ne == false
#guard Direction.nw.adjacent .se == false

-- 自身は隣接しない
#guard Direction.ne.adjacent .ne == false
#guard Direction.se.adjacent .se == false
#guard Direction.sw.adjacent .sw == false
#guard Direction.nw.adjacent .nw == false

-- ============================================================
-- Direction.isEast / isWest
-- ============================================================

#guard Direction.ne.isEast == true
#guard Direction.se.isEast == true
#guard Direction.sw.isEast == false
#guard Direction.nw.isEast == false

#guard Direction.ne.isWest == false
#guard Direction.se.isWest == false
#guard Direction.sw.isWest == true
#guard Direction.nw.isWest == true

-- ============================================================
-- LayerIndex.verticallyAdjacent
-- ============================================================

#guard LayerIndex.verticallyAdjacent 0 1 == true
#guard LayerIndex.verticallyAdjacent 1 0 == true
#guard LayerIndex.verticallyAdjacent 1 2 == true
#guard LayerIndex.verticallyAdjacent 2 1 == true
#guard LayerIndex.verticallyAdjacent 2 3 == true
#guard LayerIndex.verticallyAdjacent 3 2 == true

-- 離れたレイヤは垂直に隣接しない
#guard LayerIndex.verticallyAdjacent 0 2 == false
#guard LayerIndex.verticallyAdjacent 0 3 == false
#guard LayerIndex.verticallyAdjacent 1 3 == false

-- 自身は隣接しない
#guard LayerIndex.verticallyAdjacent 0 0 == false

-- ============================================================
-- QuarterPos.getQuarter / setQuarter
-- ============================================================

private def testLayer1 : Layer := Layer.mk
    (.crystal .red) (.crystal .red) .empty .empty

-- getQuarter: 有効な位置
#guard (QuarterPos.getQuarter (.single testLayer1) ⟨0, .ne⟩) == some (.crystal .red)
#guard (QuarterPos.getQuarter (.single testLayer1) ⟨0, .sw⟩) == some .empty

-- getQuarter: 無効な位置 (レイヤ外)
#guard (QuarterPos.getQuarter (.single testLayer1) ⟨1, .ne⟩) == none

-- setQuarter: 象限の置き換え
#guard (QuarterPos.setQuarter (.single testLayer1) ⟨0, .ne⟩ .empty) ==
    Shape.single (Layer.mk .empty (.crystal .red) .empty .empty)

-- ============================================================
-- shatterOnCut: 切断による砕け散り
-- ============================================================

-- 仕様書の例1: "crcrcrcr" → "" (全砕け)
-- 全象限が赤結晶で1クラスタ → 東西に跨がる
#guard (Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red))).shatterOnCut ==
    Shape.single emptyLayer

-- 仕様書の例2: "crRgSbcr" → "--RgSb--"
-- NE(cr) と NW(cr) が隣接同色で結合 → 東西に跨がる
#guard (Shape.single (Layer.mk (.crystal .red) (.colored .rectangle .green) (.colored .star .blue) (.crystal .red))).shatterOnCut ==
    Shape.single (Layer.mk .empty (.colored .rectangle .green) (.colored .star .blue) .empty)

-- 仕様書の例3: "CrcgcgWu" → "Cr----Wu"
-- SE(cg) と SW(cg) が隣接同色で結合 → 東西に跨がる
#guard (Shape.single (Layer.mk (.colored .circle .red) (.crystal .green) (.crystal .green) (.colored .windmill .uncolored))).shatterOnCut ==
    Shape.single (Layer.mk (.colored .circle .red) .empty .empty (.colored .windmill .uncolored))

-- 仕様書の例4: "crcrP---:--cgcg--" → "----P---:--------"
-- L1:NE(cr)-SE(cr) 同色同レイヤ結合, L2:SE(cg)-SW(cg) 同色同レイヤ結合
-- L1:SE(cr)-L2:SE(cg) 上下結合 → 全結晶が1クラスタ → 東西に跨がる
#guard (Shape.double
    (Layer.mk (.crystal .red) (.crystal .red) .pin .empty)
    (Layer.mk .empty (.crystal .green) (.crystal .green) .empty)).shatterOnCut ==
    Shape.double
    (Layer.mk .empty .empty .pin .empty)
    emptyLayer

-- 仕様書の非砕け例1: "crcgcrcg" (異色交互) → 変化なし
-- 4つの独立結晶、東西に跨がらない
#guard (Shape.single (Layer.mk (.crystal .red) (.crystal .green) (.crystal .red) (.crystal .green))).shatterOnCut ==
    Shape.single (Layer.mk (.crystal .red) (.crystal .green) (.crystal .red) (.crystal .green))

-- 仕様書の非砕け例2: "crcrcgcg" → 変化なし
-- {NE(cr), SE(cr)} = East のみ, {SW(cg), NW(cg)} = West のみ
#guard (Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .green) (.crystal .green))).shatterOnCut ==
    Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .green) (.crystal .green))

-- ============================================================
-- shatterOnCut: 追加テスト
-- ============================================================

-- 結晶を含まないシェイプ → 変化なし
#guard (Shape.single (Layer.mk (.colored .circle .red) (.colored .circle .red) (.colored .circle .red) (.colored .circle .red))).shatterOnCut ==
    Shape.single (Layer.mk (.colored .circle .red) (.colored .circle .red) (.colored .circle .red) (.colored .circle .red))

-- 空シェイプ → 変化なし
#guard (Shape.single emptyLayer).shatterOnCut == Shape.single emptyLayer

-- 単一結晶 (東側のみ) → 砕けない
#guard (Shape.single (Layer.mk (.crystal .red) .empty .empty .empty)).shatterOnCut ==
    Shape.single (Layer.mk (.crystal .red) .empty .empty .empty)

-- 単一結晶 (西側のみ) → 砕けない
#guard (Shape.single (Layer.mk .empty .empty (.crystal .red) .empty)).shatterOnCut ==
    Shape.single (Layer.mk .empty .empty (.crystal .red) .empty)

-- NE-NW 結合 (東西跨ぎ) → 砕ける
#guard (Shape.single (Layer.mk (.crystal .blue) .empty .empty (.crystal .blue))).shatterOnCut ==
    Shape.single emptyLayer

-- SE-SW 結合 (東西跨ぎ) → 砕ける
#guard (Shape.single (Layer.mk .empty (.crystal .green) (.crystal .green) .empty)).shatterOnCut ==
    Shape.single emptyLayer

-- ============================================================
-- shatterOnFall: 落下による砕け散り
-- ============================================================

-- 全象限が落下対象 → 全結晶砕け
#guard (Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red))).shatterOnFall
    (QuarterPos.allValid (.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red)))) ==
    Shape.single emptyLayer

-- 非脆弱象限がある場合 → 結晶のみ砕ける
-- "crCr----" 全落下 → "--Cr----"
#guard (Shape.single (Layer.mk (.crystal .red) (.colored .circle .red) .empty .empty)).shatterOnFall
    [⟨0, .ne⟩, ⟨0, .se⟩, ⟨0, .sw⟩, ⟨0, .nw⟩] ==
    Shape.single (Layer.mk .empty (.colored .circle .red) .empty .empty)

-- 部分的な落下: NE のみ落下対象、NE(cr)-SE(cr) が結合 → クラスタ全体砕け
#guard (Shape.single (Layer.mk (.crystal .red) (.crystal .red) .empty .empty)).shatterOnFall
    [⟨0, .ne⟩] ==
    Shape.single emptyLayer

-- 落下対象でも非脆弱なら砕けない
#guard (Shape.single (Layer.mk (.colored .circle .red) .empty .empty .empty)).shatterOnFall
    [⟨0, .ne⟩] ==
    Shape.single (Layer.mk (.colored .circle .red) .empty .empty .empty)

-- 上下レイヤの結合伝播: L1:NE(cr) 落下 → L2:NE(cg) も砕ける
#guard (Shape.double
    (Layer.mk (.crystal .red) .empty .empty .empty)
    (Layer.mk (.crystal .green) .empty .empty .empty)).shatterOnFall
    [⟨0, .ne⟩] ==
    Shape.double
    (Layer.mk .empty .empty .empty .empty)
    (Layer.mk .empty .empty .empty .empty)

-- ============================================================
-- shatterOnCut のレイヤ数保存
-- ============================================================

-- 砕け散りでレイヤ数は変わらない
#guard (Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red))).shatterOnCut.layerCount == 1
#guard (Shape.double
    (Layer.mk (.crystal .red) (.crystal .red) .pin .empty)
    (Layer.mk .empty (.crystal .green) (.crystal .green) .empty)).shatterOnCut.layerCount == 2

-- ============================================================
-- 180° 回転と shatterOnCut の可換性テスト
-- ============================================================

-- 仕様書の例1: "crcrcrcr" (全砕け)
#guard (Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red))).shatterOnCut.rotate180
    == (Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red))).rotate180.shatterOnCut

-- 仕様書の例2: "crRgSbcr"
#guard (Shape.single (Layer.mk (.crystal .red) (.colored .rectangle .green) (.colored .star .blue) (.crystal .red))).shatterOnCut.rotate180
    == (Shape.single (Layer.mk (.crystal .red) (.colored .rectangle .green) (.colored .star .blue) (.crystal .red))).rotate180.shatterOnCut

-- 仕様書の例3: "CrcgcgWu"
#guard (Shape.single (Layer.mk (.colored .circle .red) (.crystal .green) (.crystal .green) (.colored .windmill .uncolored))).shatterOnCut.rotate180
    == (Shape.single (Layer.mk (.colored .circle .red) (.crystal .green) (.crystal .green) (.colored .windmill .uncolored))).rotate180.shatterOnCut

-- 仕様書の例4: "crcrP---:--cgcg--" (2レイヤ)
#guard (Shape.double
    (Layer.mk (.crystal .red) (.crystal .red) .pin .empty)
    (Layer.mk .empty (.crystal .green) (.crystal .green) .empty)).shatterOnCut.rotate180
    == (Shape.double
    (Layer.mk (.crystal .red) (.crystal .red) .pin .empty)
    (Layer.mk .empty (.crystal .green) (.crystal .green) .empty)).rotate180.shatterOnCut

-- 非砕け例1: "crcgcrcg" (異色交互)
#guard (Shape.single (Layer.mk (.crystal .red) (.crystal .green) (.crystal .red) (.crystal .green))).shatterOnCut.rotate180
    == (Shape.single (Layer.mk (.crystal .red) (.crystal .green) (.crystal .red) (.crystal .green))).rotate180.shatterOnCut

-- 非砕け例2: "crcrcgcg" (東西分離)
#guard (Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .green) (.crystal .green))).shatterOnCut.rotate180
    == (Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .green) (.crystal .green))).rotate180.shatterOnCut

-- 空シェイプ
#guard (Shape.single emptyLayer).shatterOnCut.rotate180
    == (Shape.single emptyLayer).rotate180.shatterOnCut

-- 結晶なし
#guard (Shape.single (Layer.mk (.colored .circle .red) (.colored .circle .red) (.colored .circle .red) (.colored .circle .red))).shatterOnCut.rotate180
    == (Shape.single (Layer.mk (.colored .circle .red) (.colored .circle .red) (.colored .circle .red) (.colored .circle .red))).rotate180.shatterOnCut

-- NE-NW 結合 (東西跨ぎ)
#guard (Shape.single (Layer.mk (.crystal .blue) .empty .empty (.crystal .blue))).shatterOnCut.rotate180
    == (Shape.single (Layer.mk (.crystal .blue) .empty .empty (.crystal .blue))).rotate180.shatterOnCut

-- SE-SW 結合 (東西跨ぎ)
#guard (Shape.single (Layer.mk .empty (.crystal .green) (.crystal .green) .empty)).shatterOnCut.rotate180
    == (Shape.single (Layer.mk .empty (.crystal .green) (.crystal .green) .empty)).rotate180.shatterOnCut

-- ============================================================
-- 180° 回転と shatterOnFall の可換性テスト
-- ============================================================

-- 全象限が落下対象 (全結晶)
#guard ((Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red))).shatterOnFall
    [⟨0, .ne⟩, ⟨0, .se⟩, ⟨0, .sw⟩, ⟨0, .nw⟩]).rotate180
    == (Shape.single (Layer.mk (.crystal .red) (.crystal .red) (.crystal .red) (.crystal .red))).rotate180.shatterOnFall
    ([⟨0, .ne⟩, ⟨0, .se⟩, ⟨0, .sw⟩, ⟨0, .nw⟩].map QuarterPos.rotate180)

-- NE のみ落下、NE-SE 結合
#guard ((Shape.single (Layer.mk (.crystal .red) (.crystal .red) .empty .empty)).shatterOnFall
    [⟨0, .ne⟩]).rotate180
    == (Shape.single (Layer.mk (.crystal .red) (.crystal .red) .empty .empty)).rotate180.shatterOnFall
    ([⟨0, .ne⟩].map QuarterPos.rotate180)

-- 上下レイヤ結合伝播: L1:NE(cr) 落下 → L2:NE(cg) も砕ける
#guard ((Shape.double
    (Layer.mk (.crystal .red) .empty .empty .empty)
    (Layer.mk (.crystal .green) .empty .empty .empty)).shatterOnFall
    [⟨0, .ne⟩]).rotate180
    == (Shape.double
    (Layer.mk (.crystal .red) .empty .empty .empty)
    (Layer.mk (.crystal .green) .empty .empty .empty)).rotate180.shatterOnFall
    ([⟨0, .ne⟩].map QuarterPos.rotate180)
