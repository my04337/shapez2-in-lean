# ライブラリ・ツール一覧

S2IL プロジェクトで導入済みのライブラリ・ツールの現状評価。  
対象ツールチェーン: Lean 4 `v4.29.0`

---

## 凡例

| 列 | 記号 |
|---|---|
| 利用状態 | ✅ 積極利用中 / 🔶 一部利用 / 🔷 利用可能・未活用 |
| スキル整備 | ✅ 専用スキルあり / ⚠️ 部分的にカバー / ❌ 専用スキルなし |
| ドキュメント整備 | ✅ docs/ 内に記述あり / ⚠️ 言及はあるが薄い / ❌ 未記述 |
| プロジェクト健全性 | 🟢 活発・追従良好 / 🟡 稼働中・要注意 / 🔴 停滞・非推奨 |

---

## 直接依存（lakefile.toml に明示）

| ライブラリ / ツール | リポジトリ | 固定バージョン | 利用状態 | スキル | ドキュメント | S2IL での主な活用場面 | 健全性 |
|---|---|---|---|---|---|---|---|
| **Lean 4** | `leanprover/lean4` | v4.29.0 | ✅ | ✅ lean-setup, lean-build | ✅ docs/lean/ | 言語本体。全コード | 🟢 月次リリース |
| **Mathlib4** | `leanprover-community/mathlib4` | v4.29.0 | ✅ | ✅ lean-mathlib-search, lean-simp-guide, lean-tactic-select | ✅ docs/lean/mathlib-batteries-tips.md | 補題ライブラリ全般。List/Finset 操作、ring/omega/linarith タクティク、@[simp] 補題 | 🟢 Lean と同期リリース |
| **REPL** | `leanprover-community/repl` | v4.29.0 | ✅ | ✅ lean-repl | ✅ docs/lean/ 参照, skills/lean-repl/ | フルビルドなしの即時評価、反例チェック、タクティク探索 | 🟢 Lean と同期リリース |
| **Duper** | `leanprover-community/duper` | v4.29.0 | ✅ | ✅ lean-tactic-select (Step 3), lean-proof-planning | ✅ docs/lean/duper-guide.md | 超位置推論ベースの自動定理証明器。`aesop` / `omega` で閉じない first-order ゴールへの切り札。**S2IL REPL では import 不要（デフォルトで `import Duper` 済み）。スタンドアロンファイルでは `import Duper` が必要** | 🟡 研究プロジェクト、活発だが API 不安定あり |

---

## 推移的依存（Mathlib 経由で自動取得済み・追加 import 不要）

| ライブラリ / ツール | リポジトリ | 利用状態 | スキル | ドキュメント | S2IL での主な活用場面 | 健全性 |
|---|---|---|---|---|---|---|
| **Batteries** | `leanprover-community/batteries` | 🔶 | ✅ lean-mathlib-search（batteries-catalog.md 拡充済み）、lean-simp-guide | ✅ docs/lean/mathlib-batteries-tips.md, batteries-catalog.md | List / Array / HashMap 操作の拡張補題。手書きユーティリティ補題の代替に積極活用済み | 🟢 Mathlib 内包、活発 |
| **Aesop** | `leanprover-community/aesop` | ✅ | ✅ lean-tactic-select (Step 3 強化済み) | ✅ docs/lean/aesop-guide.md, tactics/detail/自動化/aesop.md | 等変性補題の構造的な自動閉じ込み。`@[aesop]` 属性でチェーンにルール追加可能。**S2IL REPL では import 不要（`import S2IL` 済み）。スタンドアロンファイルでは `import Aesop` が必要** | 🟢 Mathlib 依存ライブラリ、活発 |
| **Plausible** | `leanprover-community/plausible` | ✅ | ✅ lean-counterexample (Step 2b), lean-proof-planning (Phase 0), lean-tactic-select | ✅ docs/lean/plausible-guide.md | `by plausible` タクティクで ∀ 命題のランダムテスト。偽定理の早期検出。**S2IL REPL では import 不要（デフォルトで `import Plausible` 済み）。スタンドアロンファイルでは `import Plausible` が必要** | 🟡 メンテ継続中、Mathlib 経由なので固定 |
| **LeanSearchClient** | `leanprover-community/LeanSearchClient` | ✅ | ✅ lean-mathlib-search で `#leansearch` / `#loogle` を活用 | ✅ skills/lean-mathlib-search/references/ | REPL 内 `#leansearch` / `#loogle` の通信バックエンド | 🟢 Mathlib に統合、活発 |
| **ProofWidgets4** | `leanprover-community/ProofWidgets4` | 🔷 | ❌ | ❌ | VS Code Infoview での証明状態の対話的可視化。Mathlib タクティクの裏側で使用 | 🟡 メンテ継続、API 変更あり |
| **importGraph** | `leanprover-community/import-graph` | 🔶 | ✅ lean-depgraph（import グラフ生成に間接利用） | ⚠️ DepGraph.lean にて利用 | import 依存グラフの生成（`DepGraph.lean` で活用中） | 🟢 活発 |
| **Qq (quote4)** | `leanprover-community/quote4` | 🔷 | ❌ | ❌ | 型付きマクロ準クォート。証明自動化マクロ開発時のみ必要 | 🟢 Mathlib が依存、活発 |
| **lean4-cli** | `leanprover/lean4-cli` | 🔷 | ❌ | ❌ | CLI サブコマンド構築（`Main.lean` / `DepGraph.lean` の CLI 部分で間接利用） | 🟢 公式提供 |

---

## 評価保留ツール

以下のツールは現時点では優先導入を見送る。

| ツール | 理由 | 再評価条件 |
|---|---|---|
| **LeanCopilot** | Python + GPU + 別プロセス依存。CI/Server 環境では非動作。S2IL ドメイン補題への学習データが薄い可能性 | GPU 環境・Python 環境が整備された場合。WSL2 + CUDA で試験導入後に判断 |
| **Paperproof** | ProofWidgets4 と機能重複あり。3,000 行超ファイルでは証明木が複雑すぎる可能性 | ProofWidgets4 活用が定着し、それでも不足を感じた時点 |

---

## バージョン追従状況

現在は Lean `v4.29.0` に固定。Lean は月次リリースのため、Mathlib と合わせた定期的なバージョンアップが健全性維持に必要。

| 対象 | 現状 | 推奨アクション |
|---|---|---|
| Lean 本体 | v4.29.0 | 証明セッション間に `lean-toolchain` + `lakefile.toml` の rev を更新 |
| Mathlib4 | v4.29.0（Lean と同期） | Lean 更新時に同時更新 |
| REPL | v4.29.0（Lean と同期） | 同上 |
| Batteries | main ブランチ（revpin 済み） | `lake update` で最新 pin に追従 |
| Aesop | master ブランチ（revpin 済み） | 同上 |
| Plausible | main ブランチ（revpin 済み） | 同上 |
| Duper | v4.29.0 | Lean バージョンと同期した rev タグを使用。API 不安定のため破壊的変更に注意 |

---

## 参考リンク

| ライブラリ | GitHub | 公式ドキュメント |
|---|---|---|
| Mathlib4 | https://github.com/leanprover-community/mathlib4 | https://leanprover-community.github.io/mathlib4_docs/ |
| Batteries | https://github.com/leanprover-community/batteries | https://leanprover-community.github.io/batteries/ |
| Aesop | https://github.com/leanprover-community/aesop | README.md 参照 |
| Plausible | https://github.com/leanprover-community/plausible | README.md / Mathlib docs 参照 |
| LeanSearchClient | https://github.com/leanprover-community/LeanSearchClient | README.md 参照 |
| Duper | https://github.com/leanprover-community/duper | README.md 参照 |
| ProofWidgets4 | https://github.com/leanprover-community/ProofWidgets4 | README.md 参照 |
