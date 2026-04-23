# 証明計画 Current Focus 整備ガイド

> 参照タイミング: 新規証明計画（`docs/plans/{name}-proof-plan.md`）を策定するとき、
> または既存計画に sorry を追加・完了したとき

---

## 役割分担（シングルソース原則）

進行管理と実装設計は **別ファイル** に一本化する。二重管理は禁止。

| 情報の種類 | 正規の場所 | 備考 |
|---|---|---|
| 次アクション・ステップ順序・セッション末フォローアップ | `S2IL/_agent/sorry-plan.json` の `next_actions` / `remaining_steps` | 更新時はここだけを書き換える |
| 実装設計（シグネチャ候補・数学的不変量・依存補題）| `S2IL/_agent/sorry-cards/{symbol}.md` の「実装設計」セクション | 証明の中身が確定したら更新 |
| マイルストーン履歴 | `sorry-cards/{symbol}.md` 末尾の日付表 | 大きな完了時のみ 1 行追加 |
| コミット履歴・詳細な経緯 | `git log` | MD に時系列追記しない |

**禁止**:
- sorry-card に「次にやること」のステップ番号付きリストを書くこと（← sorry-plan.json と乖離する）
- sorry-plan.json にシグネチャ候補や不変量の詳細な数学的説明を書くこと（← 肥大化する）

**更新フロー**:
1. 方針を決めたら先に `sorry-plan.json` の `next_actions` / `remaining_steps` を更新
2. 新しい補題のシグネチャ候補が決まったら `sorry-cards/{symbol}.md` の「実装設計」に記録
3. ビルド通過してから `sorry-cards` マイルストーン表に 1 行追加

---

## 概要

エージェントが証明着手前に消費するコンテキストを最小化するため、
すべての証明計画ファイルは冒頭に **Current Focus** セクションを持つ。
Current Focus は「今すぐ参照すべき sorry カードへの経路」を 20 行以内で示す。

---

## 手順: 新規証明計画の作成

### ステップ 1 — 計画ファイル作成

```markdown
# {証明名} 証明計画

> 作成日: {YYYY-MM-DD}
> 最終更新: {YYYY-MM-DD}

## Current Focus

| 項目 | 値 |
|---|---|
| 対象 sorry | `{symbol_name}` |
| 位置 | `{file}:{line}` |
| カード | [`S2IL/_agent/sorry-cards/{symbol_name}.md`](../../S2IL/_agent/sorry-cards/{symbol_name}.md) |
| 構造化 | [`S2IL/_agent/sorry-plan.json`](../../S2IL/_agent/sorry-plan.json) |

**次アクション**:
1. {アクション 1}
2. {アクション 2}

詳細は `sorry-cards/{symbol_name}.md` を参照。

---

## 目標

...
```

### ステップ 2 — sorry-plan.json エントリ追加

`S2IL/_agent/sorry-plan.json` の `sorrys` 配列に追加:

```json
{
  "symbol": "{symbol_name}",
  "file": "{file}",
  "line": {line},
  "status": "sorry",
  "scope": "private",
  "statement": "{1行の数学的命題}",
  "role": "{この sorry が担う役割}",
  "plan_doc": "docs/plans/{name}-proof-plan.md",
  "history_doc": "docs/plans/{name}-proof-history.md",
  "downstream": [],
  "needed_lemmas": [],
  "blockers": [],
  "next_actions": []
}
```

### ステップ 3 — sorry-cards 作成

`S2IL/_agent/sorry-cards/{symbol_name}.md` を以下の構成で作成（クイックスタート + `<details>` 2 層構造）:

```markdown
# Sorry Card: `{symbol_name}`

> 最終更新: {YYYY-MM-DD}
> 位置: `{file}:{line}`
> スコープ: `{private|public} theorem|lemma`
> ステータス: 🟡 **{現在フェーズ}**
> **Preflight**: `.github/skills/lean-build/scripts/extract-goal-context.ps1 -File {file} -Line {line}`

---

## クイックスタート（必読 / 30-50 行）

### ゴール（要約）

```lean
{宣言の先頭 5〜10 行（長い場合は要約）}
```

宣言全体: `{file}:{line}`（symbol-map.jsonl で `endLine` 確認可）

### 次アクション（sorry-plan.json `next_actions` も参照）

1. {次に行う具体的な tactic / 補題証明の手順}
2. ...

### 直接使う補題（symbol-map.jsonl で sig 確認）

| 補題 | 役割 |
|---|---|
| `{補題名}` | ... |

### 上流

- `{呼び出し元補題}` (`{file}:{line}`): {なぜこの補題が必要か}

---

<details>
<summary>📚 詳細背景（戦略全文・実装設計・反例検証・マイルストーン）</summary>

## 証明戦略

{詳細な戦略・場合分け・数学的背景}

## 直接利用する補題（全量）

| 補題 | 役割 | ファイル |
|---|---|---|
| `{補題名}` | ... | `...` |

## 未証明の中間補題（必要なら新設）

- `{新補題名} : {型}` — {根拠と必要理由}

## 実装設計

> 進行管理（次に何をやるか・ステップの順序・セッション末のフォローアップ）は
> [`sorry-plan.json`](../sorry-plan.json) の `remaining_steps` と `next_actions` に一本化する。
> 本カードはシグネチャ候補・依存補題・数学的不変量など **実装設計** のみを保持する。

### Step {ID}: `{補題名}`

**シグネチャ候補**:
```lean
...
```

**不変量の伝播 / 証明戦略**:
- ...

## 反例検証

- {計算検証の結果を記録}

## 撤退基準

- {何セッション or 何アプローチで撤退を検討するか}

## マイルストーン

| 日付 | 追加内容 |
|---|---|
| {YYYY-MM-DD} | 新設 |

## 関連資料

- 計画: [`docs/plans/{name}-proof-plan.md`](../../../docs/plans/{name}-proof-plan.md)
- 構造化: [`sorry-plan.json`](../sorry-plan.json)
- 自動生成ビルド状態: [`sorry-goals.md`](../sorry-goals.md)

</details>
```

### ステップ 4 — sorry-goals.md 再生成

```powershell
./.github/skills/lean-build/scripts/update-sorry-goals.ps1
```

（または `build.ps1` 実行で自動生成される）

### ステップ 5 — docs/plans/README.md 追記

| ファイル | 概要 |
|---|---|
| `{name}-proof-plan.md` | {概要} |

---

## 手順: sorry が解消されたとき

1. 計画ファイルの Current Focus テーブルから当該 sorry を削除し、次の sorry に更新する。
2. `sorry-plan.json` の対象エントリを `"status": "proved"` に変更し、`downstream` を確認する。
3. `sorry-cards/` の当該ファイルは保持（参照履歴として）。
4. `update-sorry-goals.ps1` を再実行して `sorry-goals.md` を更新する。
5. `symbol-map.jsonl` に新証明済みシンボルを反映（`build.ps1` で自動再生成）。

---

## 計画ファイル作成基準（`docs/plans/README.md` の再掲）

- **作成する**: 複数 sorry（3 個以上）を含む大規模証明、または数週間以上続く作業
- **作成しない**: 1〜2 sorry の小規模証明（`docs/s2il/` に知見メモとして記録）
- **ファイル名**: `{操作名}-proof-plan.md` / `{操作名}-proof-history.md` のペアで管理

---

## チェックリスト（新規計画 + Current Focus 整備）

```
[ ] docs/plans/{name}-proof-plan.md に Current Focus セクション（先頭）
[ ] S2IL/_agent/sorry-plan.json にエントリ追加
[ ] S2IL/_agent/sorry-cards/{symbol_name}.md 作成
[ ] update-sorry-goals.ps1 実行 → sorry-goals.md 更新確認
[ ] docs/plans/README.md にファイル追記
[ ] (初回 sorry のみ) Scratch/_state/{symbol_name}.json を空テンプレートで作成
```
