# 証明計画 Current Focus 整備ガイド

> 参照タイミング: 新規証明計画（`docs/plans/{name}-proof-plan.md`）を策定するとき、
> または既存計画に sorry を追加・完了したとき

---

## 役割分担（シングルソース原則）

進行管理と実装設計は **別ファイル** に一本化する。二重管理は禁止。

| 情報の種類 | 正規の場所 | 備考 |
|---|---|---|
| 次アクション・ステップ順序・セッション末フォローアップ | `S2IL/_agent/sorry-plan.json` の `next_actions` / `remaining_steps` | 更新時はここだけを書き換える |
| コミット履歴・詳細な経緯 | `git log` | MD に時系列追記しない |

**禁止**:
- sorry-card に「次にやること」のステップ番号付きリストを書くこと（← sorry-plan.json と乖離する）
- sorry-plan.json にシグネチャ候補や不変量の詳細な数学的説明を書くこと（← 肥大化する）

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
| 構造化 | [`S2IL/_agent/sorry-plan.json`](../../S2IL/_agent/sorry-plan.json) |

**次アクション**:
1. {アクション 1}
2. {アクション 2}

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

### ステップ 3 — sorry-goals.md 再生成

```powershell
./.github/skills/lean-tooling/scripts/update-sorry-goals.ps1
```

（または `build.ps1` 実行で自動生成される）

### ステップ 4 — docs/plans/README.md 追記

| ファイル | 概要 |
|---|---|
| `{name}-proof-plan.md` | {概要} |

---

## 手順: sorry が解消されたとき

1. 計画ファイルの Current Focus テーブルから当該 sorry を削除し、次の sorry に更新する。
2. `sorry-plan.json` の対象エントリを `"status": "proved"` に変更し、`downstream` を確認する。
3. `update-sorry-goals.ps1` を再実行して `sorry-goals.md` を更新する。

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
[ ] update-sorry-goals.ps1 実行 → sorry-goals.md 更新確認
[ ] docs/plans/README.md にファイル追記
[ ] (初回 sorry のみ) Scratch/_state/{symbol_name}.json を空テンプレートで作成
```
