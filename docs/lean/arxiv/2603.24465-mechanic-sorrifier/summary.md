# Mechanic: Sorrifier-Driven Formal Decomposition Workflow for Automated Theorem Proving

- 作成日: 2026-04-13
- 最終更新: 2026-04-13
- arXiv: [2603.24465v1](https://arxiv.org/abs/2603.24465v1)

> **出典**: Ruichen Qiu et al., "Mechanic: Sorrifier-Driven Formal Decomposition Workflow for Automated Theorem Proving", arXiv:2603.24465v1 (2026-03-25)  
> **ライセンス**: [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)  
> このドキュメントは上記論文の要約・分析であり、CC BY 4.0 の帰属表示条件に従います。

---

## 1. 論文要約

### 背景と課題

LLM ベースの自動定理証明 (ATP) は進歩しているが、複雑な数学的推論に対し一発で正しい証明を生成することは困難である。失敗時の既存アプローチには 2 つの問題がある:

| アプローチ | 問題点 |
|---|---|
| **全破棄 + 再生成** (Informal Decomposition) | ほぼ正しい証明を局所的エラーで全て捨ててしまい計算資源が無駄になる |
| **反復修正** (Iterative Fix) | コンテキストが肥大化し、モデルの注意が残存サブ問題に行き届かなくなる |

### Mechanic の提案

**Sorrifier** を核とする新しいエージェントシステム **Mechanic** を提案。Lean の `sorry` プレースホルダを活用し、失敗した証明の**エラー箇所のみ**を `sorry` に置換して、周囲の正しい証明構造を保存する。

### 全体ワークフロー（4 段階）

```
1. Informal Prove
   Reasoner が自然言語の証明スケッチを生成 → Verifier が検証 → 反復改善
   ↓
2. Formal Prove
   Prover が Lean 証明を生成 → コンパイラフィードバックで修正（最大 4 ラウンド）
   ↓
3. Subgoal Split
   Sorrifier がエラー箇所を sorry に置換 → 各 sorry からサブゴール抽出 → Assemble
   ↓
4. Subgoal Process
   各サブゴールに対して 1–3 を再帰的に適用。同一サブゴールの無限ループ検知あり
```

### コンポーネント構成

| コンポーネント | 役割 |
|---|---|
| **Reasoner** (LLM) | 非形式証明スケッチ生成、サブゴール抽出時の前提合成 |
| **Verifier** (LLM) | 非形式証明品質評価、形式証明の論理・戦略評価、サブゴールの正確性・健全性検証 |
| **Prover** (LLM) | 非形式→形式変換、エラーフィードバックに基づく証明修正 |
| **Sorrifier** (ツール) | エラー箇所の反復的 sorry 置換（内側優先）。カスケードエラー防止のため 1 置換ごとに再コンパイル |
| **Lean Toolkit** | コンパイラ検証、Mathlib 定理検索 |

### Sorrifier のアルゴリズム詳細

1. コンパイルエラーの**最内側** (innermost) を特定
2. `have` ブロック内のエラー → そのブロックの証明のみを `sorry` に置換
3. ブロック外のエラー → エラー行で切り詰めて `sorry` を追記
4. **1 つ置換するたびに再コンパイル**してカスケードエラーを解消
5. コンパイル成功まで反復

### サブゴール抽出の品質保証

抽出されたサブゴールは 2 段階評価を受ける:

1. **構文検証** (Lean): 構文的に正しくコンパイル可能か
2. **意味評価** (Verifier LLM): 抽出の正確性 + 論理的健全性。反例が明白なサブゴールは拒否

### 実験結果

| ベンチマーク | 結果 |
|---|---|
| **Putnam 2025** | 12 問中 11 問解決。平均 114 分・$18.5 で他手法を大幅に凌駕 |
| **IMO 2025** | 4 問中 4 問解決。難問ほど効率差が拡大（P1 で Seed の約 1/3 の時間） |

**証明木の特徴**: Mechanic の証明木は「浅く広い」構造。同レベルの証明を並列化できるため効率的。

### アブレーション結果

- **Informal proof なし**: 簡単な問題にはオーバーヘッドだが、難問では形式証明のエラーが増加 → 証明木が肥大化
- **モデル差**: Gemini 3.1 Pro / Claude 4.5 Opus で 4/4 正解。DeepSeek 3.2 Reasoner 等は 1/4 だが、Sorrifier パイプラインにより 0 → 1 に改善

---

## 2. S2IL プロジェクトへの示唆（分析日: 2026-04-13）

### 2.1 直接適用可能なアイデア

#### (A) Sorrifier アルゴリズムの手動ワークフロー化 — ✅ 適用済み (2026-04-13)

S2IL の sorry 解消ワークフローは既に sorry-first 分解を採用しているが、Mechanic の **「最内側エラー優先 + 1 置換ごとの再コンパイル」** パターンはより体系的。

**具体的適用**:
- ビルドエラーが多数出た場合、最内側の `have` ブロックから 1 箇所ずつ sorry 化して再ビルド → カスケードエラーを除去してから取り組む
- `lean-proof-planning` スキルの Gate 2 に「Sorrifier パターン」として統合済み。Gate 3 にもビルドエラー時のカスケード除去手順を追記

#### (B) サブゴール健全性の事前検証 — ✅ 適用済み (2026-04-13)

Mechanic は抽出したサブゴールの**反例チェック**を LLM Verifier で行う。S2IL では既に `lean-counterexample` スキルで反例チェックを行っているが、**サブゴール抽出直後**に反例チェックを挟む明示的なゲートはない。

**具体的適用**:
- `lean-proof-planning` の Gate 2 に「分解後の各サブゴールに対する個別反例チェック」を**必須ステップ**として追加済み
- 早期検出チェックリストにも「各 sorry の反例チェック」をサブゴール単位の個別検証として明記

#### (C) 「証明木の浅さ」を設計目標にする — ✅ 適用済み (2026-04-13)

Mechanic は証明木が浅く広いほど効率的であることを実証。S2IL の手動証明でも、深いネスト（`have` の中に `have` の中に `have`...）を避け、可能なら独立した補題に分離することで:
- ビルド時間の短縮
- sorry 個別解消の並列化

`lean-proof-planning` の Gate 2 に「証明木は 3 レベル以内」の設計ガイドラインを追加済み。早期検出チェックリストにも深さ確認項目を追記

### 2.2 設計思想としての参考

#### (D) Informal → Formal の 2 段階パイプライン — ✅ 適用済み (2026-04-13)

Mechanic の証明プロセスはまず自然言語で証明スケッチを書き、それをガイドに形式証明を構成する。S2IL では `docs/plans/` の考察ドキュメントがこれに相当するが、**個別 sorry ごとの非形式スケッチ**を `/memories/session/` に明示的に書いてからタクティクに取り掛かる習慣にすると、方向性の迷走を防げる。

`lean-proof-planning` の Gate 2 に「各 sorry の非形式スケッチ」ステップを追加済み。`session-memory-guide.md` のテンプレートにも「Informal Sketches」セクションを追加

#### (E) 終了条件の明示 — ✅ 適用済み (2026-04-13)

Mechanic は「同一サブゴールが再帰的に出現した場合に進捗なしと判定して撤退」という明示的な終了条件を持つ。S2IL の撤退閾値（8 回試行）と相補的に使える:
- 同一ゴール状態が再出現 → 戦略変更トリガー
- N 回戦略変更後に解決不能 → 撤退

`lean-proof-progress` スキルのレッドフラグに「同一ゴール状態の再出現」を追加済み。`AGENTS.md` の撤退閾値セクションにも明記

#### (F) 検索ツールによる `unknown identifier` 解消 — ✅ 適用済み (2026-04-13)

Mechanic は `unknown identifier` エラーに対してセマンティック検索で Mathlib 定理を検索し、正しい名前を提供する。S2IL では `lean-mathlib-search` スキルと `#loogle` / `#leansearch` がこれに対応するが、**ビルドエラーの種別に応じた自動ルーティング**は参考になる。

`lean-diagnostics` スキルに「エラー種別 → 対応スキル/ツール ルーティング」テーブルを追加済み。`unknown identifier` → `lean-mathlib-search`、`type mismatch` → REPL #check、`unsolved goals` → `lean-goal-advisor` 等の判断フローを体系化

### 2.3 適用が難しい点

| 要素 | 理由 |
|---|---|
| LLM Verifier による 3 回独立評価 | S2IL はエージェント（≠ 専用 ATP モデル）であり、3 回独立検証のコストが高い |
| 16 ラウンドの非形式証明生成 | 問題の性質が異なる（コンテスト数学 vs ゲーム仕様の形式化） |
| Sorrifier の全自動パイプライン | 現状の Lean REPL + 手動ワークフローではツール統合が必要 |

---

## 3. 精読用 目次・セクションガイド

### 3.1 論文構成（セクション番号 → 内容マップ）

| §      | タイトル | ページ概算 | 読むべき人 |
|--------|---------|-----------|-----------|
| §1     | Introduction | 2p | 全員。問題設定と Informal vs Formal Decomposition の比較図（Figure 1）が核心 |
| §2     | Related Works | 1p | ATP 分野の先行研究サーベイ。ざっと読めばよい |
| §3     | Methods | 3p | **精読推奨**。Sorrifier アルゴリズム + 4 段階ワークフロー |
| §3.1   | Components | 1p | 3 LLM + Lean Toolkit + Sorrifier の役割定義 |
| §3.2   | Algorithm | 2p | 4 段階の詳細。Figure 2・3 が中心 |
| §3.2.1 | Informal Prove | 0.5p | Generate-and-Verify ループ |
| §3.2.2 | Formal Prove | 0.5p | エラー修正戦略（検索ルーティング + Verifier コメント） |
| §3.2.3 | Subgoal Split | 1p | **最重要**。Sorrify → Extract → Assemble の 3 ステップ |
| §3.2.4 | Subgoal Process | 0.5p | 再帰的分解 + 終了条件 |
| §4     | Experiments | 2p | Putnam 2025, IMO 2025 の定量結果 |
| §4.1   | Main Results | 1.5p | Table 1, 2 + Figure 4（証明木の深さ比較） |
| §4.2   | Ablation Study | 0.5p | Informal proof の必要性 + モデル差 |
| §5     | Conclusion | 0.5p | 要約 + Limitations |
| App.A  | Brief Introduction to Lean | 0.5p | Table 4: Lean タクティク一覧。Lean 初心者向け |
| App.B  | Real Examples | 2p | B.1: サブゴール論理エラーの例、B.2: IMO P3 の実証明、B.3: 証明木可視化 |
| App.C  | Implementation Details | 3p | C.1: 実験設定、C.2: **Sorrifier アルゴリズム**（疑似コード）、C.3: プロンプト集 |

### 3.2 推奨読み順（目的別）

#### Sorrifier の仕組みを理解したい

> §1 (Figure 1) → §3.1 (Sorrifier 節) → §3.2.3 (Subgoal Split, Figure 3) → App.C.2 (疑似コード)

#### S2IL の sorry ワークフロー改善に活用したい

> §3.2.3 → §3.2.4 → §4.2 (Ablation) → 本ドキュメント §2 (S2IL への示唆)

#### 実験結果と他手法との比較を確認したい

> §4.1 (Table 1, 2) → Figure 4 → §4.2

#### プロンプトエンジニアリングの参考にしたい

> App.C.3 全体（C.3.1–C.3.7 の全プロンプト）

---

## 4. 逆引きインデックス

### 概念 → セクション

| 知りたいこと | 参照先 |
|---|---|
| sorry とは何か | App.A, §3.1 (Sorrifier 節) |
| Sorrifier のアルゴリズム | §3.1 (Sorrifier 節), App.C.2 |
| カスケードエラーの処理 | §3.1 (Sorrifier 節) |
| サブゴール抽出の仕組み | §3.2.3 (Extract ステップ) |
| サブゴール品質検証（反例チェック） | §3.2.3 (Extract の 2 段階評価) |
| 証明を元に戻す (Assemble) | §3.2.3 (Assemble ステップ) |
| 再帰的サブゴール処理 | §3.2.4 |
| 無限ループ防止 | §3.2.4 |
| Informal → Formal 変換 | §3.2.1, §3.2.2 |
| unknown identifier の修正 | §3.2.2 |
| 証明木の浅さ vs 深さ | §4.1 (IMO 2025), Figure 4 |
| Putnam 2025 の結果 | §4.1 (Table 1) |
| IMO 2025 の結果 | §4.1 (Table 2) |
| モデル差（Gemini / Claude / DeepSeek 等） | §4.2 (Table 3b) |
| Informal proof の必要性 | §4.2 (Table 3a) |
| 実際の証明例（IMO P3） | App.B.2 |
| 論理エラーのあるサブゴールの例 | App.B.1 |
| 証明木の可視化 | App.B.3, Figure 5 |
| 全プロンプト | App.C.3 |

### 用語 → 定義箇所

| 用語 | 定義箇所 | 説明 |
|---|---|---|
| Sorrifier | §3.1 | エラー箇所を sorry に置換するツール |
| Sorrify / Sorrifying | §3.1, §3.2.3 | 不正なコードを sorry で置換する操作 |
| Reasoner | §3.1 | 非形式証明生成・前提合成を行う LLM |
| Verifier | §3.1 | 品質評価・論理検証を行う LLM |
| Prover | §3.1 | 形式証明生成・修正を行う LLM |
| Sorried proof | §3.2.3, Figure 1 | sorry を含むがコンパイルは通る不完全な証明 |
| Cascading errors | §3.1 | 1 つの論理的欠陥が下流に大量の偽エラーを発生させる現象 |
| Proof tree | §4.1, Figure 4 | 定理→サブゴールの分解構造を木として表現したもの |
| Informal decomposition | §1, Figure 1(a) | 自然言語レベルで問題を再分析する従来アプローチ |
| Formal decomposition | §1, Figure 1(b) | 形式証明内のエラー箇所のみを sorry で分離する本論文のアプローチ |

---

## 5. 関連研究チートシート

論文中で比較されている主要システム:

| システム | 特徴 | 参照 |
|---|---|---|
| **AlphaProof** | RL ベース、IMO 2024 銀メダル | (Hubert et al., 2026) |
| **Hilbert** | Informal → Formal の再帰的証明構築 | (Varambally et al., 2026) |
| **Aristotle** | IMO レベルの ATP | (Achim et al., 2025) |
| **Axiom** | マルチエージェントアンサンブル | (Axiom Math Team, 2025) |
| **Seed-Prover 1.5** | 大規模 RL による形式証明器 | (Chen et al., 2025a) |
| **Numina-Lean-Agent** | コーディングエージェントの数学転用 | (Liu et al., 2026) |
| **Aletheia** | 研究レベル数学へのアプローチ | (Feng et al., 2026) |
| **DeepSeek-Prover V2** | RL + サブゴール分解 | (Ren et al., 2025) |
| **Goedel-Prover** | 全証明生成モデル | (Lin et al., 2025a) |
