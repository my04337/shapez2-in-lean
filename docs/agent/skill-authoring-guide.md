# Agent Skills 記述ガイド

エージェントがスキルを新規作成・改善する際に参照するリファレンス。
簡潔さと正確さを優先し、エージェントのコンテキスト消費を最小化する構成とする。

---

## 0. 情報の鮮度と最新情報について
このドキュメントは 2026-03-28 時点の Agent Skills Open Standard を基に作成されている。
Agent Skills の仕様はまだ発展途上であり、将来的に変更される可能性がある。
最新の仕様やベストプラクティスについては以下の公式リソースを参照することを推奨する:
- [Agent Skills Specification](https://agentskills.io/specification) — Agent Skills Open Standard (agentskills/agentskills)

## 1. スキルとは

スキルは **`SKILL.md` を含むフォルダ** である。
エージェントに特定タスクの専門知識・手順・スクリプトを提供する軽量フォーマット。

```
skill-name/
├── SKILL.md          # 必須: メタデータ + 指示
├── scripts/          # 任意: 実行可能コード
├── references/       # 任意: 参照ドキュメント
├── assets/           # 任意: テンプレート・リソース
└── ...
```

### 配置場所

| スコープ | パス | 用途 |
|---|---|---|
| プロジェクト | `.github/skills/<name>/` | GitHub Copilot 用（本プロジェクト採用） |
| プロジェクト | `.agents/skills/<name>/` | クロスクライアント互換 |
| ユーザー | `~/.agents/skills/<name>/` | 全プロジェクト共通 |

> VS Code + GitHub Copilot 環境では `/skills` を入力してスキル一覧を確認できる。

---

## 2. Progressive Disclosure（段階的開示）

スキルはコンテキスト効率のため **3 段階** でロードされる:

| 段階 | ロード内容 | タイミング | トークンコスト |
|---|---|---|---|
| 1. カタログ | `name` + `description` | セッション開始時 | 〜50–100 tokens/skill |
| 2. 指示本文 | `SKILL.md` 全文 | スキル発動時 | < 5000 tokens 推奨 |
| 3. リソース | scripts / references / assets | 指示が参照した時 | 必要分のみ |

**設計原則**: `SKILL.md` 本文は **500 行以下** に収める。詳細は `references/` に分離する。

---

## 3. SKILL.md フォーマット

### 3.1 フロントマター（YAML）

```yaml
---
name: skill-name
description: >
  スキルの機能説明。Use when: トリガー条件をキーワード列挙。
---
```

| フィールド | 必須 | 制約 |
|---|---|---|
| `name` | Yes | 1–64 文字。小文字英数字とハイフンのみ。先頭・末尾ハイフン不可。連続ハイフン不可。**親ディレクトリ名と一致必須** |
| `description` | Yes | 1–1024 文字。何をするか＋いつ使うか |
| `license` | No | ライセンス名 or 同梱ファイル参照 |
| `compatibility` | No | 1–500 文字。環境要件（ツール・ランタイム等） |
| `metadata` | No | 任意の key-value マップ |
| `allowed-tools` | No | スペース区切りの事前承認ツール一覧（実験的） |

#### name の例

```yaml
# ✅ 有効
name: pdf-processing
name: data-analysis
name: lean-build

# ❌ 無効
name: PDF-Processing   # 大文字不可
name: -pdf             # 先頭ハイフン不可
name: pdf--processing  # 連続ハイフン不可
```

### 3.2 本文（Markdown）

フロントマターの後に Markdown で指示を記述する。フォーマット制約はない。
エージェントがタスクを遂行するために有用な内容を書く。

推奨セクション構成:

```markdown
# スキルタイトル

## 前提条件
- 必要なツール・依存スキル

## 手順
1. ステップ 1
2. ステップ 2
3. ...

## トラブルシューティング
- エラー A → 対処法
- エラー B → 対処法
```

---

## 4. description の書き方

`description` はスキル発動の **唯一の判断材料**。ここが不十分だとスキルは呼ばれない。

### 原則

| ルール | 説明 |
|---|---|
| 命令形で書く | `"Use when..."` パターンで発動条件を明示 |
| ユーザー意図を記述 | 内部実装ではなく、ユーザーが達成したいことを書く |
| 具体的キーワードを含める | エージェントはキーワードマッチで判断する |
| 簡潔に保つ | 数文〜短い段落。1024 文字上限 |

### 良い例 / 悪い例

```yaml
# ✅ 良い: 機能 + トリガーキーワード
description: >
  Lean 4 プロジェクトを lake build でビルドする。
  Use when: build lean project, compile lean code, lake build,
  check compilation errors, resolve build failures.

# ❌ 悪い: 曖昧すぎる
description: ビルドを手伝う。
```

### description のテスト方法

1. should-trigger / should-not-trigger のクエリを各 8–10 件用意
2. エージェントにクエリを投げ、スキルが発動するか観察
3. 失敗パターンから description を改善し再テスト
4. 5 回程度の反復で十分

---

## 5. ベストプラクティス

### 5.1 実体験から作る

汎用知識ではなく **プロジェクト固有の専門知識** をスキルに落とし込む。

- 実タスクでうまくいった手順を抽出
- エージェントを修正した箇所を記録
- 内部ドキュメント・レビューコメント・障害対応履歴を素材にする

### 5.2 コンテキストを節約する

> スキル本文のすべてのトークンは、会話履歴・システムコンテキストと競合する。

| 方針 | 詳細 |
|---|---|
| エージェントが知らないことだけ書く | PDF の説明や HTTP の基礎は不要 |
| 適切な粒度で設計する | 狭すぎ → 複数スキル同時発動。広すぎ → 誤発動 |
| 中程度の詳細さ | 網羅的ドキュメントより簡潔なステップ + 実例が勝る |
| 大きなスキルは分割 | 本文 < 500 行。詳細は `references/` に移し、参照条件を明記 |

### 5.3 制御の強さを調整する

| 状況 | アプローチ |
|---|---|
| 複数手法が有効 | 理由（why）を説明し、エージェントの判断に委ねる |
| 操作が脆弱・順序厳守 | exact コマンドを指定し「変更するな」と明記 |
| ツール選択肢がある | デフォルトを 1 つ決め、代替は簡潔に言及 |

### 5.4 反復改善する

1. 実タスクでスキルを実行
2. 成功・失敗の両方を確認（エージェントの実行トレースを読む）
3. 曖昧な指示・不要な指示を特定し修正
4. 再実行で検証

---

## 6. 効果的な指示パターン

### 6.1 Gotchas（落とし穴）セクション

エージェントが **知らなければ間違える** 環境固有の事実を列挙する。
汎用アドバイス（「エラーを適切に処理せよ」）ではなく具体的な訂正情報。

```markdown
## Gotchas

- `sorry` は Lake 出力では `warning` として報告される。
  メッセージに `declaration uses 'sorry'` を含むもののみ sorry として分類する。
- `lake build` の終了コード 0 はエラーなしを意味しない。
  stderr に warning が含まれている場合がある。
```

**ヒント**: エージェントがミスした都度、その訂正を Gotchas に追記する。

### 6.2 出力テンプレート

出力フォーマットが重要な場合、散文で説明するよりテンプレートを提供する。

````markdown
## 出力フォーマット

```json
{"file":"<path>","line":<n>,"severity":"<error|warning|info>","message":"<msg>"}
```
````

### 6.3 チェックリスト

複数ステップのワークフローでは、進捗追跡と手順漏れ防止にチェックリストを使う。

```markdown
## ワークフロー

- [ ] Step 1: 入力ファイルを検証
- [ ] Step 2: 変換を実行
- [ ] Step 3: 出力を検証
- [ ] Step 4: 結果を報告
```

### 6.4 バリデーションループ

作業後にバリデーションを走らせ、失敗時は修正→再検証のサイクルを指示する。

```markdown
1. 編集を行う
2. バリデーション実行: `scripts/validate.sh`
3. 失敗した場合:
   - エラーメッセージを確認
   - 修正
   - 再度バリデーション
4. パスするまで繰り返す
```

### 6.5 Plan-Validate-Execute

破壊的・バッチ操作では中間計画 → 検証 → 実行の 3 段階を踏む。

---

## 7. スクリプト設計

### 7.1 配置と参照

スクリプトは `scripts/` に配置し、`SKILL.md` からの相対パスで参照する。

```markdown
## 利用可能スクリプト

- **`scripts/build.ps1`** — ビルド実行（Windows）
- **`scripts/build.sh`** — ビルド実行（macOS / Linux）
```

### 7.2 エージェント向けスクリプト設計原則

| 原則 | 理由 |
|---|---|
| 対話プロンプト禁止 | エージェントは非対話シェルで動作する。全入力はフラグ/stdin で受ける |
| `--help` を実装 | エージェントがインターフェースを学習する主要手段 |
| 構造化出力を使う | JSON / CSV 等、パース可能な形式を stdout に出力 |
| 診断は stderr へ | stdout のデータと進捗メッセージを分離 |
| 明確なエラーメッセージ | 何が間違い、何が期待値で、何を試すべきか |
| べき等性 | エージェントはリトライする。「なければ作成」が安全 |
| ドライラン対応 | 破壊的操作は `--dry-run` フラグでプレビュー |
| 出力サイズを予測可能に | 巨大出力はサマリーをデフォルトにし、`--verbose` で詳細を提供 |

### 7.3 クロスプラットフォーム対応

本プロジェクトでは OS ごとにスクリプトを用意するパターンを採用:

```
scripts/
├── build.ps1    # Windows (PowerShell)
└── build.sh     # macOS / Linux (bash)
```

`SKILL.md` 内で OS 別の実行方法を明記するか、OS 判定ロジックをスクリプト内に持たせる。

---

## 8. 品質評価（Eval）

### 8.1 テストケース設計

```json
{
  "skill_name": "my-skill",
  "evals": [
    {
      "id": 1,
      "prompt": "リアルなユーザープロンプト",
      "expected_output": "成功時の出力の説明",
      "files": ["evals/files/input.txt"],
      "assertions": [
        "出力に X が含まれる",
        "ファイル Y が生成される"
      ]
    }
  ]
}
```

- 2–3 件から開始し、結果を見て拡張
- フレーズ・詳細度・エッジケースを変える
- 現実的なコンテキスト（ファイルパス・カラム名等）を含める

### 8.2 評価ループ

1. with_skill / without_skill の 2 構成で各テストを実行
2. アサーションを PASS/FAIL で採点（根拠を記録）
3. 結果を集計し delta（スキルの効果）を算出
4. 人間レビューで定性的な問題を捕捉
5. フィードバックを `SKILL.md` に反映し再実行

### 8.3 改善の指針

- 両構成で常に PASS するアサーション → 削除（スキルの価値を示さない）
- 両構成で常に FAIL → アサーション自体を修正
- with_skill のみ PASS → スキルが価値を発揮している箇所。理由を分析
- why（理由）ベースの指示が rigid なルールより効果的

---

## 9. GitHub Copilot での注意事項

| 項目 | 詳細 |
|---|---|
| スキルディレクトリ | `.github/skills/<name>/` が Copilot のネイティブ配置先 |
| 発見確認 | チャットで `/skills` を入力しスキル一覧に表示されるか確認 |
| モデル差異 | モデルによりスキル発動の信頼性が異なる。ツール実行せず直接回答する場合あり |
| スクリプト実行権限 | エージェントがターミナルコマンド実行時に許可を求める場合がある |
| フロントマター注意 | コロンを含む値はクォートする: `description: "Use when: ..."` |

---

## 10. チェックリスト: スキル作成時

新規スキル作成時に確認する項目:

- [ ] `name` が親ディレクトリ名と一致している
- [ ] `name` が小文字英数字 + ハイフンのみで構成されている
- [ ] `description` に機能説明 + `Use when:` トリガーキーワードが含まれている
- [ ] `description` が 1024 文字以内
- [ ] `SKILL.md` 本文が 500 行以下（超過分は `references/` に分離）
- [ ] エージェントが知らない情報のみ記述されている
- [ ] 手順が具体的で再現可能
- [ ] スクリプトがある場合、`--help` とエラーメッセージが実装されている
- [ ] `/skills` でスキルが発見されることを確認済み
- [ ] 実タスクで発動・実行を検証済み

---

## 出典

- [Agent Skills Specification](https://agentskills.io/specification) — Agent Skills Open Standard (agentskills/agentskills)
- [What are skills?](https://agentskills.io/what-are-skills) — Agent Skills Open Standard
- [Best practices for skill creators](https://agentskills.io/skill-creation/best-practices) — Agent Skills Open Standard
- [Optimizing skill descriptions](https://agentskills.io/skill-creation/optimizing-descriptions) — Agent Skills Open Standard
- [Using scripts in skills](https://agentskills.io/skill-creation/using-scripts) — Agent Skills Open Standard
- [Evaluating skill output quality](https://agentskills.io/skill-creation/evaluating-skills) — Agent Skills Open Standard
- [Adding skills support to your agent](https://agentskills.io/client-implementation/adding-skills-support) — Agent Skills Open Standard
- [GitHub: agentskills/agentskills](https://github.com/agentskills/agentskills) — ソースリポジトリ

Agent Skills Open Standard のコードは Apache 2.0、ドキュメントは CC-BY-4.0 でライセンスされている。

## 作成情報

- **作成日**: 2026-03-28
- **適用ライセンス**: 本ドキュメント自体は MIT（プロジェクトライセンスに準拠）
