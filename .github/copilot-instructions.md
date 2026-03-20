# Copilot Instructions - Shapez2 in Lean

## 応答言語
- 日本語で応答する

## プロジェクト概要
- **正式名称**: Shapez2 in Lean（略称: **S2IL**）

## 参照ドキュメント一覧

エージェントは推論時に必要に応じて以下を参照すること。

### Shapez2 ゲーム用語
| ファイル | 内容 |
|---|---|
| `docs/shapez2/glossary.md` | ゲーム内用語集（シェイプ・建物・操作など） |

### Lean 4 ・数学
| ファイル | 内容 |
|---|---|
| `docs/lean/lean-reference-guide.md` | Lean 4 言語仕様リファレンスの索引（文法・型・タクティクなど） |
| `docs/lean/theorem-proving-guide.md` | 定理証明の実践ガイド（タクティク・帰納型・再帰など） |
| `docs/lean/fp-in-lean-guide.md` | 関数型プログラミング in Lean ガイド |
| `docs/lean/math-glossary.md` | 数学用語辞書（型理論・論理学・代数構造など） |
| `docs/lean/toolchain-guide.md` | ツールチェインガイド（elan・Lake・Lean 等の役割） |

## コーディング規約
- 文字コード: UTF-8 (BOMなし)。ただしBOMが必要な場合はBOMを付ける
- 改行コード: CRLF
- コメントは日本語で記述
- インデント: スペース4つ
- 新規ファイルには以下の SPDX ヘッダを追加
  ```lean
  -- SPDX-FileCopyrightText: <作成年> my04337
  -- SPDX-License-Identifier: MIT
  ```
  - 新規作成: `<作成年>` = 現在の年（例: 2026）
  - 大幅改変: 範囲表記に更新（例: 2018-2026）
  - 既存ファイルに SPDX ヘッダが無い場合、追加しない

## Lean 4 命名規則
- 型・構造体・クラス・帰納型: `UpperCamelCase`（例: `NatColor`, `MyStructure`）
- 定理・補題: `lowerCamelCase`（例: `addComm`, `zeroAdd`）
- 関数・定義: `lowerCamelCase`（例: `toString`, `getSize`）
- 名前空間: `UpperCamelCase`（例: `Nat`, `List`）
- 略語は先頭以外大文字にしない（例: `httpRequest` ではなく `HttpRequest`）
- ドット記法を活用し、型名を名前空間として関数を定義（例: `List.map`）
- `Prop` を返す述語は `is` / `has` 接頭辞を使用（例: `isEven`, `hasDecEq`）

## 外部ライブラリのライセンス方針
- **利用可**: パブリックドメイン、MIT-0 等（義務なし）
- **要確認**: MIT, BSD-2, BSD-3, MPL 2.0 等（著作権・許諾表示が必要）
- **利用厳禁**: GPL, AGPL, LGPL 等コピーレフト系、商用ライブラリ、ライセンス不明・制限が厳しいもの
