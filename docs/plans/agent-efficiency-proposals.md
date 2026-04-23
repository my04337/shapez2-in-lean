# エージェント効率化提案

- 作成日: 2026-04-23
- 最終更新: 2026-04-23（第55報: 案 O/P 適用効果を #54/#55 で実測 → **定着判定**。案 I/J を Tier 1 基盤に昇格。新規案 Q（caller-invariant preflight）追加）
- ステータス: **Tier 1 基盤（案 A/D/E/F/I/J/N） / Tier 1.5 案 H/K/L/O/P 定着 / 案 M パイロット未着手 / 新規案 Q 追加**
- 関連: `AGENTS.md` §検索、`.github/skills/lean-build/SKILL.md`、`docs/agent/proof-retreat-pivot-guide.md`

## 背景

Lean4 中〜大規模プロジェクトでのエージェントのコンテキスト消費（特に `read_file` による大ファイル入力）を削減するため、複数案を比較検討。本書は Tier 1（適用済）→ Tier 1.5（活用率引き上げ）→ Tier 2/3（未適用・条件付き）を一本化して管理する。

## 累積成果（第43〜55報）

| 指標 | #43 | #44 | #46 | #49 | #51 | #52 | #53 | #54 | **#55** | 目標 |
|---|---|---|---|---|---|---|---|---|---|---|
| sig-digest 経由率 | 0% | ~25% | ~60% | 🔴 0% | 🟢 ~100% | 🟢 ~90% | 🟡 対象外* | 🟢 ~100% | 🟢 ~100% | 70% |
| symbol-map `endLine` 活用率 | — | 0% | ~80% | ~80% | ~80% | ~80% | —* | 🟢 ~90% | 🟢 ~90% | 70% |
| extract-goal-context 直接利用率 | 0% | 0% | 0% | 0% | 0% | 0% | 0% | 0% | 0% | — |
| sorry-card 事前埋込参照率（案 J） | — | — | — | — | 🟢 100% | 🟢 100% | 🟢 100% | 🟢 100% | 🟢 100% | 70% |
| 大ファイル `read_file` 総回数 | 7 | 15 | 7 | 8 | 🟢 4 | 🟢 ~6 | 🟢 **0** | 🟢 ~5 | 🟡 ~8 | 6〜8 |
| pivot / 撤退品質 | — | — | — | 🟢 | 🟢 | 🟢 | n/a | n/a | 🟢 | 継続 |

\* #53 は「会話要約からの継続セッション」という特殊ケース。

**#54 の傾向**（案 O/P 適用セッション）: scaffold 抽出（`placeLDGroups_landing_groundingEdge_mono` 補題新設）+ agent 効率化ツール更新（symbol-map に `digest`/`endLine` 追加 = 案 E 拡張、AGENTS.md に build フック chain 表追加 = 案 P、preflight 緩和例外追加 = 案 O）。Lean ソース read ~5 回に抑制。

**#55 の傾向**（本セッション・d'≥2 closure）: sorry-card の「クイックスタート」+「候補補題（事前抽出）」+「case d'=1 戦略記述」だけで d'≥2 分岐を一発実装。`landingDistance_not_occupied_at_landing` の直接適用で閉鎖、単発 build エラー 1 件（`List.mem_cons_self _ _` → 引数なし版）を即修正。想定外だった項目は **caller invariant 調査**: d'=1 の命題真偽を検証するため `ProcessWave.lean:106` の `mergeSort by LD` を直接 read する必要があり、反例分析（4-layer unsorted ケース）から「aux シグネチャに sort-by-LD 前提が未伝播」を crystallize。この発見は sorry-card に事前埋込があれば避けられた可能性があり、**新規案 Q 追加**。

---

## Tier 1（即時適用済み）

| 案 | 実装物 | 状態 |
|---|---|---|
| 案 1 + 案 4 | `S2IL/_agent/sig-digest/<dotted>.md`（build 成功時自動再生成）| ✅ 定着 |
| 案 8 | `.github/skills/lean-build/scripts/extract-goal-context.ps1` | ✅ 定着（直接起動は案 J 経由に置換）|
| 案 6 | AGENTS.md セッション圧縮ルール（3 ファイル / 30 ターン / 2 ラウンド閾値）| ✅ 定着 |

---

## Tier 1.5: 活用率引き上げ施策

### 案 A: AGENTS.md 検索チェックリスト階層化 ✅ **定着**

`read_file` 前の preflight として 200 行超 → sig-digest 必須化。sig-digest 経由率を 0% → 25% → ~100% に引き上げた基盤施策。

---

### 案 D: セッション冒頭 preflight ルール ✅ **定着**

「証明作業セッションの最初の tool call 前に sig-digest を少なくとも 1 本 read せよ」。案 I で境界条件を補強済。

---

### 案 E: symbol-map に `digest` / `endLine` 追記 ✅ **定着**

`symbol-map.jsonl` の各エントリに sig-digest 相対パスと次宣言の 1 行前を付与。`read_file(startLine=line, endLine=endLine)` でピンポイント読みを実現。

**#51 実績**: `placeLDGroups_landing_groundingEdge_mono_step` (line 934, endLine 1076) や本補題 (line 1077, endLine 1183) を 1 ショットで取得。範囲過剰読みゼロ。

---

### 案 F: 大ファイル preflight hook ✅ **定着（案 I で補強）**

「直近 3 ターン以内に当該ファイルの sig-digest を read 済か自己チェック」。案 I 併用で「過去セッション既知」錯覚による後退を防止。

---

### 案 H: sorry-card の 2 層分離 ✅ **適用済（#51 効果確認）**

**施策**: クイックスタート（上位 30〜50 行）+ `<details>` 折畳の詳細背景。

**#51 実績**: `placeLDGroups_landing_groundingEdge_mono.md` の冒頭 50 行だけで「ステータス・障害・次アクション」を取得でき、pivot 判断ができた。ただし障害分析フェーズでは `<details>` 内部を read する必要があり、**クイックスタートは意思決定に有効、詳細は分析フェーズで必要** という 2 モード使い分けが確立。

**残課題**: 詳細部（200 行超）はエディタ開封時に依然全量流入 → 案 M で対応検討。

---

### 案 I: セッション冒頭「過去知識スキップ禁止」ルール ✅ **定着（#51 で効果確認）**

**#51 実績**: セッション冒頭から sig-digest (GroundedMono / LandingDist) を先行 read。sig-digest 経由率 0% (#49) → ~100% (#51) に回復。Lean ソース `read_file` 8 回 → 4 回に半減。**目標 70% を大幅に上回り達成**。

---

### 案 J: sorry-card への extract-goal-context 出力の事前埋込 ✅ **定着（#51 で効果確認）**

**#51 実績**: sorry-card の「候補補題（事前抽出）」セクション（Shape / groundingEdge_base / foldl_placeFU_mixed_fixed_d_groundingEdge_mono / pin_singleton_landing_empty 等 13 本）を読むだけで候補補題ファイル行を取得でき、`extract-goal-context.ps1` の明示起動ゼロで同等情報を獲得。**案 G 失敗からの pivot 成功**。

**残課題**: 現状は手動更新のため、sorry 移動や依存補題追加時に陳腐化リスク → 案 N で恒久化。

---

### 案 K: 撤退 / pivot 判断テンプレート ✅ **定着**

**#51 試験導入 → #52 で案 L に吸収しガイドライン化、#53 で適用機会なしだが sorry-card マイルストーン記述テンプレとして生きている**。次の pivot 発生時に使われる見込み。

---

### 案 L（#52 適用済）: pivot テンプレートの正式ガイドライン化 ✅ **定着**

**適用**: `docs/agent/proof-retreat-pivot-guide.md` (105 行) を #52 で作成し `docs/agent/README.md` からリンク。撤退チェックリスト / マイルストーン記述テンプレート / `pending-required` 等ステータス使い分け / 事例集 (#49, #51) を収録。

**#53 効果**: 本セッションでは pivot 未発生のため直接参照はなしだが、sorry-card / sorry-plan.json の remaining_steps ステータス（`done` / `pending-recommended` / `pending-required` / `pending-next` / `pending-if-needed`）はガイドライン通り使分けされており、文書フォーマットとして定着していると判定。

---

### 案 N（#52 適用済）: sorry-card 事前埋込の build フック統合 ✅ **定着**

**適用**: `build.ps1` の成功フック chain (sig-digest · symbol-map · sorry-goals ・伝統) に `update-sorry-card-context.ps1` を追加。同スクリプトの regex bug も #52 で修正済み。

**#53 効果**: 本セッション末尾の `lake build` 成功時に、sorry 位置が L1052 → L1153 に移動したにも関わらず sorry-card の候補補題セクションが自動追従（手動起動ゼロ）。案 J の陣腐化リスクが恒久的に除去されたことを確認。

**施策**: `docs/agent/proof-retreat-pivot-guide.md`（新設、50〜80 行）に以下を記載:
1. 撤退判断チェックリスト（反例 / 循環依存 / scaffold 構造 / REPL 失敗）
2. sorry-card マイルストーン表の記載テンプレート（報番 / 種別 / 発見方法 / 性質 / pivot 提案 の 5 項目）
3. sorry-plan.json `remaining_steps` への新 step 追加ルール（`pending-required` / `pending-if-needed` / `pending-recommended` の使い分け）
4. 過去事例集: #49 (Plan A scaffold 障害) / #51 (step lemma 再利用不能)

**期待効果**: pivot 判断の質・記録が標準化され、「何が試されたか」の再発防止が機能。

**GO/NOGO**: 🟢 **GO**。実装コスト < 30 行の新規ドキュメント、次セッション冒頭で作成可能。

---

### 案 M（#51 追加）: sorry-card 詳細部の分離ファイル化 🟡 **条件付き GO・保留継続**

**発端**: 案 H 適用後も `<details>` 折畳の詳細部はエディタ開封時に全量コンテキスト流入（300 行超）。

**#52〜#55 追記**: 直近 4 セッション連続で sorry-card の冒頭〜120 行で判断可能。#55 では sorry-card を `read_file(1-400)` で 1 回一括読みしており、うち実質活用は冒頭 100 行程度。起動条件（3 回以上 read × 2 セッション連続）未達継続。

**施策（不変）**: 1 枚パイロット → 運用負荷評価。

**GO/NOGO**: 🟡 **条件付き GO（保留継続）**。#55 でも読み回数 1 回、条件未達成。

---

### 案 N（上記で定着記載済み）

---

### 案 O（#53 追加・#54-#55 実測）: 会話要約継続セッションでの preflight 緩和ルール ✅ **定着**

**発端**: #53 は conversation summary からの継続セッションで、summary に「位置・コード・次アクション」が全含まれていたため Lean ソースを read せず完走。案 I（「過去セッションで読んだファイルも sig-digest を 1 回 read」）はこのケースでは過剰な事前読み。

**適用**: AGENTS.md の案 I 記述に「summary 内 4 要素完備ならスキップ可」の例外条項を追加（#54）。

**#54/#55 効果**:
- #54（scaffold 抽出）: summary 経由継続だったが「新規 scaffold 抽出」作業のため 4 要素完備は成立せず、案 I 原則通り sig-digest preflight を実施 → 正しい判定。
- #55（本セッション）: summary に位置（L1063）・コード・次アクション（d'≥2 を先に閉じる）・ビルド状態が揃っていたが、**d'=1 の命題真偽検証という「新規分析」が含まれていたため案 I 原則通り sig-digest preflight 実施** → 正しい判定。

**定着判定根拠**: 2 セッション連続で「summary 完備 / 新規判断混入」の境界線で適切に切り分けられた。境界ケースの誤判定ゼロ。

---

### 案 P（#53 追加・#54 適用）: build フック chain の AGENTS.md 明示化 ✅ **定着**

**発端**: 案 N で build.ps1 に sorry-card-context update を組み込んだが AGENTS.md / `docs/agent/README.md` に自動更新物リストが欠落。

**適用**: AGENTS.md §編集の前に `lake build 成功時の自動生成物` 表を追加（#54）。

**#54/#55 効果**: 本セッション（#55）で「手動で update-* を走らせるべきか」と迷うシーンがゼロ。build 成功後の自動更新物（sig-digest / symbol-map / sorry-goals / sorry-card 候補補題）が AGENTS.md の表通りに動作することを確認。**二重走行リスク完全除去**。

---

### 案 Q（新規・#55 追加）: sorry-card への caller-invariant 事前埋込 🟢 **GO**

**発端**: #55 で d'=1 の命題真偽を検証する際、aux シグネチャに `sort-by-LD` 前提が無いにも関わらず命題が実運用で成立する理由を確認するため、caller 側（`ProcessWave.lean:106` の `settling.mergeSort (fun a b => landingDistance a obs ≤ landingDistance b obs)`）を直接 read する必要が生じた。これは案 J（候補補題事前抽出）の延長線上で防止可能。

**施策**: sorry-card に新セクション「Caller 不変量（実運用で成立する但し aux/本補題に未伝播の前提）」を追加。内容:
- **caller ファイル:行**（例: `ProcessWave.lean:106`）
- **caller 側で確立される不変量**（例: `sortedSettling = settling.mergeSort (LD ≤)` → LD 昇順）
- **aux シグネチャに伝播済みか**（Yes/No）
- **未伝播の場合の影響**（反例 case / abstract obs 下の命題真偽）

**実装方式**: 手動記載（案 J と同様）で開始。3 セッション連続で参照率 70% 以上なら自動化（`update-sorry-card-caller-invariants.ps1` を build フック chain に追加）を検討。

**期待効果**: #55 パターン（caller 調査のため上流ファイル read）を将来的に除去。#55 では caller read 1 回（ProcessWave.lean L100-200）が発生しており、これが削減目標。

**GO/NOGO**: 🟢 **GO（#56 着手）**。初期は手動記載のみ（AGENTS.md + sorry-card テンプレートに 5 行追記）、コスト軽微。

**補足**: 自動化版のブレーンストーミング — `symbol-map.jsonl` の downstream 情報（sorry-plan.json に既存）を参照して caller ファイルを特定 → `grep_search` で当該 symbol の直前 20 行から `mergeSort` / `filter` / `sort` / `List.Sorted` / `Pairwise` を抽出 → sorry-card の caller invariant セクションに自動注入、という流れが可能。まず手動で 1-2 枚パイロット後に判断。

---

---

## Tier 2: Sorry-card クロージャ化（**NOGO 継続**）

sorry-card に REPL ゴール状態 + 周辺シグネチャを自動追記する案。

**NOGO 理由**: #51 で `read_file` 4 回（目標圏最下限）。案 E + I + J の組合せで初動費用は十分低減済。

**再評価条件**: 「sorry-card + symbol-map + sig-digest を活用しても初動 3 ターンで大ファイル read が 5 回以上」が **2 セッション連続**で観測された場合のみ着手。

---

## Tier 3: 公開 API ファサード化

| Phase | 判定 | 理由 |
|---|---|---|
| **Phase 1** (symbol-map に visibility 追加) | 🟡 条件付き GO | `"scope":"private"` 既に emit 済。残りは `public-api.jsonl` 抽出スクリプトのみ |
| **Phase 2** (新規補題 `private` 指向ガイドライン) | 🟢 GO | `docs/lean/naming-conventions.md` 追記のみ |
| **Phase 3** (`@[irreducible]` 付与 + `.Internal` 移送) | 🔴 NOGO | S1 sorry 残存中。再評価: S1 完了後 |

---

## 採用ポートフォリオ（第55報更新）

| 組み合わせ | 累積削減見込 | ステータス（#55） |
|---|---|---|
| Tier 1 のみ | 実効 0〜5% | #43 実測 |
| + 案 A+D | 実効 10〜15% | #44 実測 |
| + 案 E+F | 35〜45% | ✅ #46 実測 |
| + 案 I（セッション冒頭ルール強化） | +5〜10% | 🔵 **Tier 1 昇格（#55）** |
| + 案 J（extract-goal-context 事前埋込） | 案 G 代替 +5〜10% | 🔵 **Tier 1 昇格（#55）** |
| + 案 H（sorry-card 2 層分離） | 55〜65% | 🟢 定着 |
| + 案 K（pivot テンプレート） | 定性改善 | 🟢 定着 |
| + 案 L（pivot ガイドライン化） | 定性改善 | 🟢 定着 (#52) |
| + 案 N（sorry-card 埋込の build フック統合） | 案 J 恒久化 | 🟢 定着 (#52) |
| + 案 O（継続セッション preflight 緩和） | +少量、継続セッション限定 | 🟢 **定着 (#54/#55)** |
| + 案 P（build フック chain 明示化） | 二重走行防止 | 🟢 **定着 (#54/#55)** |
| + **案 Q**（caller-invariant 事前埋込） | +5% 見込 / caller 調査 read 除去 | 🟢 **GO（#56 着手）** |
| + 案 M（sorry-card 詳細分離） | +10〜15% | 🟡 保留継続（trigger 未達 × 4 セッション） |
| + Tier 3 Phase 1 (visibility index) | 60〜70% | 🟡 条件付き GO |
| + Tier 3 Phase 2 (private 指向) | +数% | 🟢 GO |
| + Tier 2（ゴール埋込）| — | 🔴 NOGO 継続 |
| + Tier 3 Phase 3 (`@[irreducible]`) | 70〜80% | 🔴 NOGO（S1 sorry 残存）|

**廃案**: 案 B（route-map に digest パス、案 E で代替）、案 C（汎用 snapshot 埋込、案 J に吸収）、案 G（Preflight 行提示、失敗判定）。

---

## 次の意思決定ポイント（第56報目標）

1. **[#56 着手] 案 Q**: sorry-card テンプレートに「Caller 不変量」セクションを追加し、`placeLDGroups_landing_groundingEdge_mono.md` でパイロット（caller = `ProcessWave.lean:106` の `mergeSort by LD`）。2 枚目パイロット候補は `waveStep_nonGroundedLayerSum_lt` 関連 sorry 復活時。
2. **[#55 完了] 案 I/J の Tier 1 昇格**: 5 セッション連続（#51-#55）で経由率 90% 以上 & sorry-card 事前埋込参照率 100% を達成 → 基盤案と認定。AGENTS.md の位置づけを「推奨」→「必須前提」に更新。
3. **[保留継続] 案 M**: trigger 未達 × 4 セッション連続。計測継続。起動条件を緩和するか検討（「sorry-card が 500 行超 × 2 セッション連続」等に切替）。
4. **[Tier 3 Phase 1 候補]** S1 完了（残 1 sorry）後に `public-api.jsonl` 抽出スクリプト着手。S1 完了後の最初のセッションで Phase 1/2 を評価。
5. Tier 2 は継続して NOGO。再評価条件不変。

### #55 セッション振り返り（反省点）

- ✅ sig-digest preflight を 3 本（GroundedMono / LandingDist / PlaceGrounding）先行実施、symbol-map で `endLine` 経由ピンポイント読み
- ✅ 案 J の候補補題セクションで extract-goal-context 起動ゼロ維持
- ✅ 案 O を適切に運用（「新規分析含む」判定で case I 原則に従った）
- 🟡 **caller 調査のため `ProcessWave.lean` を read**（反例検証フェーズで 1 件、~100 行）→ **案 Q で恒久化予定**
- 🟡 `List.mem_cons_self _ _` 書法のバージョン間差異で build エラー 1 件（即修正）— REPL 型確認をスキップした箇所
  - **再発防止**: 新規補題の本体書き込み前に REPL 型確認は継続すべきだが、補題内部の 1 行ヘルパー（`have ... := List.mem_cons_self`）レベルでは現状負担過大。TypeError 即修正サイクルに吸収する運用で許容。

---

## 付録: 測定データサマリ（#43〜#53）

| 報番 | 主作業 | sig-digest 経由率 | read_file (Lean) | 特記事項 |
|---|---|---|---|---|
| #43 | `waveStep_grounding_mono` scaffold | 0% | ~10 | Tier 1 活用率 0% の起点 |
| #44 | h_edge_landing 枝抽出 | ~25% | ~15 | 案 A/D 効果、補助ファイル preflight 未到達 |
| #46 | Plan A induction scaffold 実装 | ~60% | 7 | 案 E/F 適用後・read_file 半減達成 |
| #47〜48 | case2 分解・3+1 サブゴール閉鎖 | ~60% | — | sorry を GroundedMono.lean:1053 に集約 |
| #49 | SUB-A 分析・Plan A 障害発見 | 0%（後退） | 8 | 案 G 失敗判定・案 I/J/K 新規提案 |
| #50 | step lemma 0-sorry 完全証明 | — | — | 案 I/J 適用（効果は #51 で実測） |
| #51 | 案 3 障害 crystallize・案 3' 設計確定 | ~100% | 4 | 案 I/J/K/H 効果実測、新規案 L/M/N 追加 |
| #52 | `_step_generic` 抽出・案 L/N 適用 | ~90% | ~6 | proof-retreat-pivot-guide 作成・build フック chain 拡張 |
| #53 | aux-lemma 実装・会話要約続起 | 対象外* | 0 | summary から 1 sorry 追加閉鎖を Lean source read なしで達成、新規案 O/P 追加 |
| #54 | scaffold 抽出・案 O/P 適用 | ~100% | ~5 | `placeLDGroups_landing_groundingEdge_mono` 新設、symbol-map に digest/endLine 追加、AGENTS.md に build フック表追加 |
| **#55** | **d'≥2 case 閉鎖・案 Q 発案** | **~100%** | **~8** | `landingDistance_not_occupied_at_landing` 直接適用で d'≥2 一発閉鎖、caller 調査から案 Q の種を発見 |

\* #53 は会話要約からの継続で、Lean ソースを read せずに作業完走したため「sig-digest 経由」の分母も存在せず。これ自体が案 I のエッジケースとして記録されるべき事象。
