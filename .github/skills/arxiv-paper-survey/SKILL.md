---
name: arxiv-paper-survey
description: >
  Survey arXiv papers and extract S2IL-relevant insights into structured docs.
  Use when: arxiv paper, 論文要約, paper summary, survey paper, research paper,
  read paper, 論文調査, paper analysis, academic paper, 論文スキル,
  summarize arxiv, 論文を読む, paper reference, 論文リファレンス.
metadata:
  argument-hint: 'Pass arXiv URL or paper ID'
disable-model-invocation: true
---

# arXiv 論文調査スキル

arXiv 論文を読み、S2IL プロジェクトへの示唆を含む構造化ドキュメントを生成する。

## 発動条件

- ユーザーが arXiv 論文の URL または ID を提示して要約・調査を依頼した場合
- ユーザーが「論文スキル」を明示的に指定した場合

## 成果物

スキル実行後、以下のファイルが生成・更新される:

| ファイル | 場所 | 内容 |
|---|---|---|
| `summary.md` | `docs/lean/arxiv/<ID>-<短縮名>/` | 論文要約 + S2IL 示唆 + 目次 + 逆引き |
| `README.md` | `docs/lean/arxiv/<ID>-<短縮名>/` | 出典・ライセンス・利用者の義務 |
| `docs/lean/arxiv/README.md` | 更新 | 論文一覧テーブルに行追加 |
| `docs/lean/README.md` | 更新 | arXiv セクションのテーブルに行追加 |

## 手順

### Phase 1: 情報収集

1. **arXiv URL の解決**: ユーザーが ID のみを提示した場合、`https://arxiv.org/html/<ID>` を構築
2. **論文取得**: `fetch_webpage` で HTML 版を取得（PDF よりテキスト抽出が容易）
   - query: 論文タイトル + キーワード
3. **ライセンス確認**: ページ末尾に表示されるライセンス情報を確認
   - CC BY 4.0 / CC BY-SA 4.0 / CC BY-NC 等を記録
   - ライセンスが不明な場合はユーザーに確認

4. **ライセンス分類と作業続行判断**:

   | 分類 | 該当ライセンス例 | 対応 |
   |---|---|---|
   | **OSS 互換（続行可）** | CC BY 4.0 | そのまま Phase 2 へ進む |
   | **コピーレフト** | CC BY-SA 4.0, CC BY-SA 3.0 | `vscode_askQuestions` でユーザーに確認 |
   | **非 OSS / 商用禁止** | CC BY-NC 4.0, CC BY-NC-SA 4.0 | `vscode_askQuestions` でユーザーに確認 |
   | **ライセンス不明 / All Rights Reserved** | 記載なし | `vscode_askQuestions` でユーザーに確認 |

   **コピーレフト・非 OSS・不明の場合**: 以下の内容で `vscode_askQuestions` を呼び出し、ユーザーの明示的な承認を得てから Phase 2 に進むこと。承認が得られない場合は作業を中止する。

   ```
   header: "ライセンス確認"
   question: "この論文のライセンスは <ライセンス名> です。
   <ライセンスの性質の説明（例: コピーレフト条項があり、派生物を同一ライセンスで公開する必要があります / 商用利用が禁止されています / ライセンスが明示されておらず All Rights Reserved の可能性があります）>。
   要約・分析ドキュメントを生成してよいですか？"
   options: ["はい、分析を進める", "いいえ、中止する"]
   allowFreeformInput: false
   ```

### Phase 2: ディレクトリ名の決定

**命名規則**: `<arXiv番号>-<短縮タイトル>`

- arXiv 番号: `YYMM.NNNNN` 形式（例: `2603.24465`）
- 短縮タイトル: 論文タイトルから**2–4 単語**を抽出、kebab-case
- 例: `2603.24465-mechanic-sorrifier`

### Phase 3: summary.md の作成

[テンプレート](./references/summary-template.md) に従って以下のセクションを作成:

#### メタデータブロック（先頭）
`作成日` / `最終更新` / `arXiv` の直後に以下の**出典・ライセンス表示ブロック**を必ず挿入すること:

```
> **出典**: <著者筆頭> et al., "<論文タイトル>", arXiv:<ID> (<公開日>)
> **ライセンス**: [<ライセンス名>](<ライセンス URL>)
> このドキュメントは上記論文の要約・分析であり、<ライセンス略称> の帰属表示条件に従います。
```

#### §1. 論文要約
- 背景と課題（表形式で既存手法の問題点を整理）
- 提案手法（コア概念を 3–5 文で）
- 全体ワークフロー（コードブロックで視覚的に）
- コンポーネント構成（表形式）
- 主要アルゴリズムの詳細（番号付きリスト）
- 実験結果（ベンチマーク・定量値を表形式で）

#### §2. S2IL プロジェクトへの示唆
見出しに分析日を含める: `## 2. S2IL プロジェクトへの示唆（分析日: YYYY-MM-DD）`  
最も重要なセクション。3 カテゴリに分類:

| カテゴリ | 内容 | 記述方針 |
|---|---|---|
| **直接適用可能なアイデア** | 既存ワークフロー・スキルに統合できる具体策 | 「どのスキル/ドキュメントに統合するか」まで明記 |
| **設計思想としての参考** | S2IL の方針決定に影響しうる知見 | 現状との対比を含める |
| **適用が難しい点** | 前提条件の違い等で直接は使えない要素 | 理由を表形式で簡潔に |

#### §3. 精読用 目次・セクションガイド
- セクション番号 → 内容マップ（表形式、ページ概算・読むべき人を含む）
- 目的別の推奨読み順（引用ブロックで視覚的に）

#### §4. 逆引きインデックス
- 概念 → セクション（「知りたいこと | 参照先」テーブル）
- 用語 → 定義箇所（「用語 | 定義箇所 | 説明」テーブル）

#### §5. 関連研究チートシート（任意）
- 論文中で比較・言及されている主要システムの一覧表

### Phase 4: README.md の作成

[テンプレート](./references/readme-template.md) に従って出典・ライセンス情報を作成:

- 論文メタデータ（タイトル・著者・所属・arXiv ID・公開日・分類）
- ライセンス種別と条件
- 利用者の義務（ライセンス種別ごとに記述）
- 帰属表示の例文
- ファイル一覧

### Phase 5: 既存ドキュメントの更新

1. **`docs/lean/arxiv/README.md`**: 論文一覧テーブルに新しい行を追加
2. **`docs/lean/README.md`**: arXiv セクションのテーブルに新しい行を追加

### Phase 6: コミット

すべてのファイルを 1 コミットにまとめる:

```
docs: arXiv paper survey - <短縮名> (<arXiv番号>)

- docs/lean/arxiv/<ID>-<短縮名>/: new paper directory
  * README.md: citation and <ライセンス> license info
  * summary.md: comprehensive summary with S2IL insights
- docs/lean/arxiv/README.md: added to paper listing
- docs/lean/README.md: added to arXiv section
```

## 品質チェックリスト

summary.md 作成後、以下を確認:

- [ ] §2（S2IL への示唆）に具体的なスキル名・ドキュメント名が含まれているか
- [ ] 表形式が崩れていないか（Markdown テーブルの列数一致）
- [ ] 逆引きインデックスが論文の主要トピックを網羅しているか
- [ ] README.md のライセンスが論文の実際のライセンスと一致しているか
- [ ] `docs/lean/arxiv/README.md` の論文一覧に追加されているか
- [ ] `docs/lean/README.md` に追加されているか

## ライセンス別の利用者義務テンプレート

### CC BY 4.0

```markdown
1. **帰属表示 (Attribution)**: 元の著作者名、論文タイトル、arXiv リンクを明記すること
2. **変更の明示**: 原著作物から変更を加えた場合、その旨を表示すること
3. **追加制限の禁止**: 他者がライセンスで許可されている行為を制限するような法的条件や技術的手段を追加しないこと
```

### CC BY-SA 4.0

```markdown
1. **帰属表示 (Attribution)**: CC BY 4.0 と同上
2. **継承 (ShareAlike)**: 二次的著作物を作成した場合、同一ライセンスまたは互換ライセンスで公開すること
3. **追加制限の禁止**: CC BY 4.0 と同上
```

### CC BY-NC 4.0

```markdown
1. **帰属表示 (Attribution)**: CC BY 4.0 と同上
2. **非商用 (NonCommercial)**: 商業目的での利用は禁止
3. **追加制限の禁止**: CC BY 4.0 と同上
```

### ライセンス不明・All Rights Reserved

```markdown
⚠️ この論文のライセンスは明示されていません。要約はフェアユース / 引用の範囲で作成しています。
原文の大量引用・再配布は避けてください。
```

## 注意事項

- **原文のコピーは行わない**: あくまで要約・分析であり、論文テキストの大量転載はしない
- **数式・図表の説明**: 図表は言葉で説明し、必要に応じて「Figure X 参照」と記載
- **HTML 版が利用できない場合**: `fetch_webpage` で Abstract ページ (`https://arxiv.org/abs/<ID>`) を取得し、可能な範囲で要約する。HTML 版がない旨を summary.md に記載
