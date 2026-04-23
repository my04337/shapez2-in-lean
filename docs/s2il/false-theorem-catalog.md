# 偽定理カタログ

> 作成日: 2026-04-14
> 最終更新: 2026-04-24

Gravity 層の探索で発見された偽定理・偽の不変量候補をリファレンスとして集約したカタログ。  
同じ落とし穴を避けるための参照素材として保存している。  
状況・経緯・具体的な証明戦略は `docs/plans/` 側で管理するとして、ここは **「真と思えたが反例がある命題」を設計参照用に集めたリスト**として維持する。

---

## 偽定理一覧

| 偽の仮定 | なぜ偽か |
|---|---|
| `PinLandingEmpty` 不変量保存 | 5L 2dir で 16/112,882 violations。cluster→crystal 配置が後続 pin の着地先を塞ぐ |
| `one_step_all_grounded_pin` nonEmpty case (∀ obs) | 任意 obs で偽。foldl 中間状態では 0 violations。`h_step : ∀ obs'` が過度に一般的 |
| `process_rotate180` without layerCount bound (旧 waveStep) | ≥6L で偽（6L 反例あり）。**解決済み**: settling FU を事前着地距離の昇順でソートすることで全レイヤ数で等変に |
| `landingDistance_placeFU_gap` の minLayer ≤ 2 制約撤廃 | placeAbove shapes で干渉確認（128/34,322 ペア） |
| `gravity_truncate_eq_gravity_gravity_truncate` | gravity 前後で truncate 結果が異なる。一般には偽 |
| exfalso by `layerCount ≤ 10 + minLayer ≥ 3 + gap ≥ 2` | p=3, q=5, gap=2 で矛盾せず。算術的に不可 |
| `minLayer_le_two_of_placeAbove_settled` | settled 入力でも minLayer ≥ 3 FU は多数発生（maxMinLayer=3, violations=14,785） |
| `gravity_IsSettled` (≥6L) | ≥6L シェイプで偽。pin 配置が水平接地接触を切断 → 浮遊クラスタ残存 |
| ImmBelow as foldl invariant | 4,504/45,576 failures（cross-direction cluster が破壊） |
| ANEG → ImmBelow | 反例あり: `obs = [⟨cr, -, -, -⟩, ⟨cr, cr, -, -⟩]` — ANEG=true, ImmBelow=false |
| ImmBelow as dual invariant (ANEG ∧ ImmBelow) | all-empty obstacle でも 916/27,945 IB failures |
| `shouldProcessBefore_no_chain` | 4L 反例: 3 pins in same column |
| `sortFallingUnits_spb_order_preserving` | 3 要素干渉パターン: chains a→b→c |
| `sortFallingUnits_inversion_is_tied` | one-way pairs can be inverted in sortFallingUnits output |
| `B3_landing_empty_in_obs` (waveStep) | 4L/3-type で偽。結晶ボンドチェーンがピンを迂回し、settling cluster が非 settling ピン位置に着地。例: cluster[(1,NE),(1,SE),(2,SE),(3,SE),(3,NE)] + pin(2,NE) → (3,NE) が (2,NE) に着地しピン上書き。≤3L では真。main axiom は依然真 |
| `waveStep_floatingUnits_length_lt` | 10L 反例: FU count 2→2→0。非 overwrite パターン。nonGroundedLayerSum 測度に切替済み |
| `floatingUnits_waveStep_subset_nonSettling` | 9L 反例: s' の FU が fus.filter(nonSettling) に含まれない |

---

## sorry #4b に関する棄却済みアプローチ

このセクションは過去の特定 sorry に紐づく内容のため削除された。  
現在の再構築方針は [`../plans/layer-ab-rewrite-plan.md`](../plans/layer-ab-rewrite-plan.md) および [`../plans/architecture-layer-ab.md`](../plans/architecture-layer-ab.md) を参照（旧 Gravity 限定計画は [`../plans/archive/gravity-greenfield-rewrite-plan.md`](../plans/archive/gravity-greenfield-rewrite-plan.md) に退避済み）。

---

## 棄却済み不変量候補（15+ 候補の計算検証結果）

| Candidate | Violations | Status |
|---|---|---|
| ANEG alone (∀ obs) | 136/742 gp mono fail | ❌ |
| SubANEG (all vertex removal) | 105,032 | ❌ |
| BypassCrystal | 9,946 | ❌ |
| CrystalNotAP | 100,722 | ❌ |
| ConnectedComponent | 81,654 | ❌ |
| non_bridge_removal h_cycle | 22 fails | ❌ |
| PinBelowNE | 296 | ❌ |
| VGrounded | 20,632 | ❌ |
| Layer-restricted connectivity | 142,910 | ❌ |
| General NonBridge | 19,908 bridges | ❌ |
| ABF | 9,504+11,160 | ❌ |
| ColumnConnected | 21,176 | ❌ |
| DownwardReachable | 48 (4dir) | ❌ |
| Crystal-to-pin+belowNE | 1,496 | ❌ |
| PosColFull only | 68/654 | ❌ |

---

## 成功した十分条件（参考）

| 条件 | 結果 | 備考 |
|---|---|---|
| **ANEG ∧ ImmBelow → gp_mono_pin** | 0/6,860 FAIL (2L 4dir) | 十分条件としては成立。問題は ImmBelow の導出 |
| **ImmBelow at pin NE moments** | 16/16 OK (5L 2dir) | foldl 順序が emergent に保証。しかし形式証明の導出が困難 |

---

## PinLandingEmpty 偽定理の詳細

**旧アプローチ（Approach δ/ε）**: `PinLandingEmpty` 不変量を foldl で搬送し、pin 着地位置が常に空であることを保証。

**反例パターン**: cluster[(4,d1),(4,d2),(3,d2),(2,d2)] d=2 → crystal at (2,d1)、then pin(3,d1) d=1 → lands at (2,d1) where crystal exists

**対応**: `PinLandingEmpty` 関連の全定義・補題を削除。`one_step_all_grounded_pin` を `by_cases` 分岐方式に変更。

---

## 関連ドキュメント

- [gravity-equivariance-analysis.md](gravity-equivariance-analysis.md) — Gravity 証明の技術的知見
