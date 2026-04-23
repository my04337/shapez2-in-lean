# Lean 4 ツールチェインガイド

Lean 4 の開発環境を構成する主要コンポーネントの名称と役割を簡潔にまとめた資料です。

---

## コンポーネント一覧

### elan — バージョンマネージャ

Lean のバージョン管理ツール。Rust における **rustup** に相当する。

| 項目 | 内容 |
|---|---|
| 役割 | Lean コンパイラの複数バージョンをインストール・切替 |
| インストール先 | `~/.elan/` |
| 主な操作 | `elan install <version>`, `elan default <version>`, `elan show` |
| バージョン指定 | プロジェクトルートの `lean-toolchain` ファイルに記載されたバージョンを自動選択 |

```
# elan のインストール (公式)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

### Lean — コンパイラ / 型チェッカ

Lean 4 言語の中核。ソースコードの型検査・証明検証・コンパイルを行う。

| 項目 | 内容 |
|---|---|
| 実行ファイル | `lean`（型検査 / エラボレーション）, `leanc`（C コンパイラフロントエンド） |
| `lean` の役割 | `.lean` ファイルを解析し、型検査を行い `.olean`（中間形式）を生成 |
| `leanc` の役割 | Lean が生成した C コードをネイティブバイナリにコンパイル（内部で C コンパイラを呼び出す） |
| 通常の使い方 | 直接呼ぶことは稀。Lake 経由で間接的に実行される |

### Lake — ビルドシステム / パッケージマネージャ

Lean のビルドツール兼パッケージマネージャ。Rust における **Cargo** に相当する。

| 項目 | 内容 |
|---|---|
| 役割 | プロジェクトのビルド・依存解決・テスト実行 |
| 設定ファイル | `lakefile.toml`（TOML 形式）または `lakefile.lean`（Lean DSL 形式） |
| ロックファイル | `lake-manifest.json`（依存パッケージのバージョンを固定） |
| ビルド出力先 | `.lake/` ディレクトリ |

主要コマンド:

| コマンド | 用途 |
|---|---|
| `lake build` | プロジェクト全体または指定ターゲットをビルド |
| `lake build <target>` | 特定のライブラリ・実行ファイルをビルド |
| `lake exe <name>` | ビルド済み実行ファイルを実行 |
| `lake clean` | ビルド成果物を削除 |
| `lake update` | 依存パッケージを最新に更新（`lake-manifest.json` を再生成） |
| `lake init <name>` | 新規プロジェクトを初期化 |
| `lake env printPaths` | Lean のモジュール検索パス等の環境情報を出力 |

---

## プロジェクト構成ファイル

| ファイル / ディレクトリ | 役割 |
|---|---|
| `lean-toolchain` | 使用する Lean バージョンを指定（例: `leanprover/lean4:v4.28.0`）。elan がこのファイルを読み、対応するバージョンを自動ダウンロード・使用する |
| `lakefile.toml` | プロジェクト名・ライブラリ・実行ターゲット・依存パッケージを定義する設定ファイル（TOML 形式） |
| `lakefile.lean` | `lakefile.toml` の代替。Lean DSL で記述する形式。より高度な設定が可能 |
| `lake-manifest.json` | Lake が自動生成するロックファイル。依存パッケージの正確なリビジョンを記録する |
| `.lake/` | ビルド成果物（`.olean`, `.ilean`, ネイティブバイナリ等）と、ダウンロードした依存パッケージのキャッシュ。`.gitignore` に含めるべきディレクトリ |

---

## 中間ファイル形式

| 拡張子 | 名称 | 説明 |
|---|---|---|
| `.olean` | Object Lean | コンパイル済み環境データ（定義・証明・型情報等）。他のモジュールからの `import` を高速化する |
| `.ilean` | Interface Lean | `.olean` のインターフェース情報のみを含む軽量版。依存関係の並列ビルドに使用される |
| `.c` | C ソース | Lean コンパイラが生成する中間 C コード。`leanc` でネイティブバイナリにコンパイルされる |

---

## エコシステムの主要ライブラリ

| 名称 | 概要 |
|---|---|
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Lean 4 最大の数学ライブラリ。代数・解析・位相等の広範な形式化を含む |
| [Std（Batteries）](https://github.com/leanprover-community/batteries) | 標準ライブラリの拡張。データ構造・タクティク等を提供（旧名 Std4、現在は Batteries に改名） |
| [Aesop](https://github.com/leanprover-community/aesop) | 自動証明タクティク。ルールベースの探索で証明を自動構築する |
| [ProofWidgets](https://github.com/leanprover-community/ProofWidgets4) | VS Code 上でインタラクティブな証明可視化を提供するフレームワーク |
| [doc-gen4](https://github.com/leanprover/doc-gen4) | Lean 4 プロジェクトから API ドキュメントを自動生成するツール |

---

## ツール間の関係（概念図）

```
elan (バージョンマネージャ)
 └── lean-toolchain を読み、適切なバージョンの Lean / Lake を選択
      ├── lean (コンパイラ / 型チェッカ)
      │    ├── .lean → .olean / .ilean  (型検査・エラボレーション)
      │    └── .lean → .c              (コード生成)
      ├── leanc (C コンパイラフロントエンド)
      │    └── .c → ネイティブバイナリ
      └── lake (ビルドシステム)
           ├── lakefile.toml / lakefile.lean  (プロジェクト設定)
           ├── lake-manifest.json             (依存ロック)
           └── .lake/                         (ビルド出力・パッケージキャッシュ)
```

---

## 免責事項

本ドキュメントは非公式の解説資料です。Lean プロジェクトおよびその著者とは一切関係がありません。内容の正確さについて一切保証しません。本ドキュメントを参照したことによって生じたいかなる損害についても、作成者は責任を負いません。

## ライセンス

Copyright 2026 my04337

MIT License に基づいて頒布されます。ライセンスの全文は本リポジトリの [LICENSE](../../LICENSE) ファイルを参照してください。
