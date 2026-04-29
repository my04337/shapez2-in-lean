# Opus 4.7 向けエージェント・スキル設計原則

> 作成日: 2026-04-29 / 最終更新: 2026-04-29
>
> 本プロジェクトのカスタムエージェント (`.github/agents/`) とスキル (`.github/skills/`) を設計・改修する際の判断基準。
> Anthropic 公式ブログ [Best practices for using Claude Opus 4.7 with Claude Code](https://claude.com/blog/best-practices-for-using-claude-opus-4-7-with-claude-code) を本プロジェクト文脈で再解釈したもの。

---

## 1. 運用思想：「ペアプロ」から「委任」へ

Opus 4.7 はゴールと制約だけを渡せば、関連コードの探索・推論・実行を自律的にこなす。
よって設計者の仕事は **タスク手順の細分化** ではなく **ゴール・制約・受け入れ基準の明確化** になる。

| 旧モデル時代の発想 | Opus 4.7 で取るべき発想 |
|---|---|
| ステップを 1〜N 番に分解して順に従わせる | 目的・観点・I/O 仕様を渡して手段は委ねる |
| 思考プロセスを書かせて方向性を矯正する | Adaptive Thinking に任せ、必要なら "Think carefully…" 等の定型句で制御 |
| 毎回ガードレール（〜するな）を全部書く | ルートの AGENTS.md に原則を集約し、各タスクは参照のみ |
| サブエージェントを毎回明示指定する | description で「いつ・なぜ呼ぶか」を明示し、判断は本体に委ねる |
| 曖昧なレビュー依頼で気付きを集める | レビュー観点を 5〜10 個列挙して観点ベースで投げる |

---

## 2. サブエージェント設計 5 原則

Opus 4.7 はデフォルトでサブエージェントを起動しなくなった。**起動コストを上回る価値が説明できる粒度** に切る。

### 原則 1: fan-out 適性で切る

サブエージェントの存在意義は次のいずれか:

- **fan-out**: 複数の独立項目（複数 sorry / 複数ファイル）を並列に処理する
- **コンテキスト隔離**: 詳細探索を本体コンテキストから切り離し、要約だけを返す
- **専門ツールチェーン**: REPL JSONL 作成・実行・パース等の定型を内製化

これらに該当しない、本体が 1 ターンで完結できる作業（目視できる関数のリファクタ等）は **エージェント化しない**。

### 原則 2: 自律完結

main agent は「対象 sorry / ファイル / 診断ファイルパス」程度を渡すだけで結果が返ってこなければならない。
途中で main へ問い合わせるエージェントは設計失敗とみなす。

入力が不足している場合は、エージェント側で **既定値で続行** または **取得不能を summary で 1 行報告** する。

### 原則 3: 明確な I/O 仕様

`description` を **3 段構造** で書く:

```
**When**: いつこのエージェントを呼ぶか（トリガとなる状況キーワードを列挙）
**Returns**: 何を返すか（テーブル / 推奨 1 件 / 候補リスト 等）
**Don't call when**: 呼ぶべきでないケース（main 1 ターンで済む / 別エージェントの守備範囲）
```

`argument-hint` には main から渡す情報の最小セットを 1 行で示す（例: `sorry symbol name + sorry-plan.json path`）。

### 原則 4: 短い summary 返却

main agent は要約のみ受け取れば十分。エージェントは:

- 結果テーブル（最大 10 行程度）
- 推奨アクション（1〜3 件）
- 検証済み副作用（変更ファイル等）

の 3 点に絞った Markdown を返す。詳細ログは `Scratch/` や JSONL に残し、要約から参照させる。

### 原則 5: 副作用境界の明示

`tools` フィールドで副作用を制限する:

- 調査専門: `[execute, read, search]`（コード編集なし）
- 編集可: `[execute, read, edit, search]`
- 連鎖必要: 上記 + `agent`

エージェント本文の最初に「プロダクションコードを編集する／しない」を 1 行で明示する。

---

## 3. スキル設計 3 原則

Opus 4.7 はツール呼び出しも控えめ。スキルは **能動的な手順実行装置** ではなく **参照ドキュメント** として再定義する。

### 原則 1: 参照特化

スキルは次のいずれかに絞る:

- **カタログ系**: ゴール形状 → タクティク／補題のマッピング表（例: `lean-tactic-select`, `lean-mathlib-search`）
- **ハンドブック系**: ツール（REPL / build / diag）の使い方リファレンス（例: `lean-repl`, `lean-build`, `lean-diagnostics`）
- **ガイド系**: 設計判断の指針（例: `lean-proof-planning`, `lean-simp-guide`）

「タスクを走らせる」役割はサブエージェントに移譲する。

### 原則 2: description は When + Returns

```yaml
description: >
  <一行サマリ>. Use when: <トリガ語句をカンマ区切りで列挙>.
```

トリガ語句には **日本語と英語の両方** を入れる（プロジェクト言語が混在するため）。
反例: 「Use when: 〜したいとき」のような曖昧な日本語のみは避ける。

### 原則 3: エージェントとの責務分離

同名・同領域のエージェントが存在するスキルは、本文を **エージェントが参照する詳細リファレンス** として書き直す（手順は持たせず観点と表だけ）。
エージェントとスキルが両方走る重複構成は禁止。

---

## 4. 指示文の書き方

### Adaptive Thinking 制御

固定的な「思考プロセスを書け」は廃止。必要なときだけ次の定型句で制御する:

- 深く考えさせたい: `Think carefully and step-by-step before responding; this problem is harder than it looks.`
- 速く返させたい: `Prioritize responding quickly rather than thinking deeply. When in doubt, respond directly.`

### ネガティブ指示よりポジティブ例示

| 悪い例 | 良い例 |
|---|---|
| 「コメントを過剰に追加するな」 | 「変更行のみコメントを追加し、既存行のコメントは変えない」 |
| 「リファクタするな」 | 「依頼された範囲だけを変更する。改善案は別タスクとして提案する」 |
| 「ツール呼び出しを減らせ」 | 「`grep_search` は同一クエリで 1 回まで。`No matches` のときのみ `includeIgnoredFiles: true` で再試行」 |

### 応答長の明示

短く返したい / 構造化させたいときは prompt 末尾で形式を指定する:

> Return as a Markdown table with columns: `#`, `tactic`, `result`, `remaining goals`. Limit to 8 rows.

---

## 5. ハンドオフ設計

`handoffs` は **真に独立した次工程** のみ列挙する。連鎖を main 任せにすることで:

- main がコンテキスト全体を見て次を選べる
- handoff 時のメッセージ重複が減る
- エージェント間の循環依存を防げる

`handoffs[].prompt` は **テンプレート変数 + 1 文の依頼** に留め、ゴール仕様は前段の summary に含めて main から渡す前提とする。

---

## 6. 実装チェックリスト（新規・改修時）

- [ ] `description` が When / Returns / Don't call when の 3 段で書かれているか
- [ ] `argument-hint` が 1 行で main → agent の I/O を表現しているか
- [ ] 本文に「Step 1〜N」の細かい手続きが残っていないか（残すのは順序が真に重要な箇所のみ）
- [ ] ネガティブ指示がポジティブ例示に置き換わっているか
- [ ] スキルとエージェントで責務が重複していないか
- [ ] 副作用境界（`tools` フィールド + 本文 1 行明示）が揃っているか
- [ ] サブエージェントを呼ぶ場合、handoff 候補が main の判断に委ねられる形で列挙されているか

---

## 7. 関連ドキュメント

- [custom-agent-guide.md](custom-agent-guide.md) — カスタムエージェント仕様（フロントマター・ファイル配置）
- [skill-authoring-guide.md](skill-authoring-guide.md) — スキル仕様（Progressive Disclosure・SKILL.md 構造）
- [agent-operations-playbook.md](agent-operations-playbook.md) — 運用手順（PowerShell / シェル規約）
- [proof-retreat-pivot-guide.md](proof-retreat-pivot-guide.md) — 撤退・pivot 判断
