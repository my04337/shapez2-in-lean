# 偽定理カタログ

> 作成日: 2026-04-14
> 最終更新: 2026-04-14

Gravity 等変性証明チェーンの過程で発見された偽定理・棄却済みアプローチの一覧。
同じ落とし穴を避けるためのリファレンスとして保存する。

---

## 偽定理一覧

| 偽の仮定 | なぜ偽か |
|---|---|
| `PinLandingEmpty` 不変量保存 | 5L 2dir で 16/112,882 violations。cluster→crystal 配置が後続 pin の着地先を塞ぐ |
| `one_step_all_grounded_pin` nonEmpty case (∀ obs) | 任意 obs で偽。foldl 中間状態では 0 violations。`h_step : ∀ obs'` が過度に一般的 |
| `process_rotate180` without layerCount bound | ≥6L で偽（6L 反例あり）。≤5L では 1.9M+ shapes で 0 failures |
| `landingDistance_placeFU_gap` の minLayer ≤ 2 制約撤廃 | placeAbove shapes で干渉確認（128/34,322 ペア） |
| `gravity_truncate_eq_gravity_gravity_truncate` | gravity 前後で truncate 結果が異なる。一般には偽 |
| exfalso by `layerCount ≤ 10 + minLayer ≥ 3 + gap ≥ 2` | p=3, q=5, gap=2 で矛盾せず。算術的に不可 |
| `minLayer_le_two_of_placeAbove_settled` | settled 入力でも minLayer ≥ 3 FU は多数発生（maxMinLayer=3, violations=14,785） |
| `gravity_IsSettled` (≥6L) | ≥6L シェイプで偽。pin 配置が水平接地接触を切断 → 浮遊クラスタ残存 |
| ImmBelow as foldl invariant | 4,504/45,576 failures（cross-direction cluster が破壊） |
| ANEG → ImmBelow | 反例あり: `obs = [⟨cr, -, -, -⟩, ⟨cr, cr, -, -⟩]` — ANEG=true, ImmBelow=false |
| ImmBelow as dual invariant (ANEG ∧ ImmBelow) | all-empty obstacle でも 916/27,945 IB failures |

---

## sorry #4b 棄却済みアプローチ一覧

sorry #4b（`all_grounded_settle_foldl` 内 pin NE コールバック）に対して
11 のアプローチを検証し、すべて棄却した。Plan B（axiom 化）の根拠となった記録。

| # | アプローチ | 結果 | 棄却理由 |
|---|---|---|---|
| 1 | ImmBelow foldl invariant | ❌ | 4,504 failures (cross-direction cluster) |
| 2 | ANEG alone → pin preservation | ❌ | 水平 detour 不可 |
| 3 | non_bridge_removal | ❌ | groundingEdge は directed → detour 構成不能 |
| 4 | native_decide | ❌ | 3^20 ≈ 3.5B 状態空間 (5L 4dir) |
| 5 | Direct grounding path 構成 | ❌ | adj positions の接地に ImmBelow 必要 |
| 6 | by_cases on ImmBelow(obstacle) | △ | Case True の step case が cluster で失敗 |
| 7 | Local ImmBelow conditions | ❌ | 全列で ImmBelow 必要 |
| 8 | ANEG → ImmBelow at pin NE | ❌ | ANEG ↛ ImmBelow（反例確認済） |
| 9 | per-position landing tracking | 未実施 | ~800-1000 行・3-4 セッション（唯一の未棄却候補） |
| 10 | one_step_all_grounded_pin 書換 | ❌ | ImmBelow は必要条件 |
| 11 | dual invariant (ANEG ∧ ImmBelow) | ❌ | all-empty でも 916 IB failures |

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

- [gravity-proof-execution-plan.md](../plans/gravity-proof-execution-plan.md) — Plan B の実行計画
- [gravity-equivariance-analysis.md](gravity-equivariance-analysis.md) — Gravity 証明の技術的知見
