# Gravity Greenfield Rewrite 計画

- 作成日: 2026-04-24
- 最終更新: 2026-04-24
- ステータス: **計画策定フェーズ / 実装未着手**
- スコープ: `S2IL/Operations/Gravity/` 以下（振る舞い系: 落下・結晶砕け散り・安定化）の再構築
- 上位計画: [`MILESTONES.md`](MILESTONES.md) Layer B

---

## 0. この計画のゴール

次の 3 条件をすべて満たす状態へ Gravity 層を作り直す。

1. **公開 API と internal 補題の境界が明確** で、外部からは Gravity.lean facade だけを参照すればよい
2. **同じ意味を持つ補題が複数存在しない**（特に `_rotateCW_comm` / `_rotate180_comm` のような等変性の並行チェーンを排除）
3. **使われなくなった補題を検出・除去する流れが組み込まれている**

既存の証明資産は捨てずに、上記の原則に照らして **再利用可否を判定した上で** 新構造へ取り込む。

---

## 1. 基本原則

### 1.1 単一チェーン原則（等変性）

回転群 $\mathbb{Z}/4\mathbb{Z}$ は CW 回転 1 つから生成される。したがって各操作の等変性は **CW 回転との可換性 1 本だけ**を主証明とし、他の回転（180° / CCW）は機械的に導出する:

$$f(s.\mathrm{rotate180}) = f(s.\mathrm{rotateCW}.\mathrm{rotateCW}) = f(s).\mathrm{rotateCW}.\mathrm{rotateCW} = f(s).\mathrm{rotate180}$$

この書き換えを `rotate180_eq_rotateCW_rotateCW`（既存、`Kernel/Transform/Rotate.lean`）で行う。 `_rotate180_comm` は 1 行の系として書き、独自の証明を持たせない。

**禁止事項**: 操作 `f` について、`f_rotateCW_comm` と `f_rotate180_comm` それぞれに独立した帰納法・場合分け証明を書くこと。

### 1.2 MECE 原則（層分割）

Gravity 層の内容物は次の 5 種類に MECE 分割する。層をまたぐ補題は書かない:

| 層 | 数学的対象 |
|---|---|
| Basic | `floatingUnits` / `settling` の集合論的性質 |
| Descent | `landingDistance` の step-wise 意味論 |
| Place | `placeFallingUnit` / `placeLDGroups` の length・layerCount 保存 |
| WaveStep & Process | 1 波の進行と終端性 |
| Equivariance | CW 回転との可換性（単一チェーン） |

### 1.3 真偽検証先行原則

すべての補題・定理は、証明着手前に次のいずれかで**真と判明するまで signature を確定しない**:

1. `lean-theorem-checker` で valid Shape 反例検索
2. REPL `#eval` / `plausible` でランダム検証
3. 数学的導出（既存の真定理からの含意）

偽と判明した命題は即座に signature を修正し、再検証する。**scaffold として sorry を書く前に必ず検証する**。

### 1.4 デッド補題クリーンアップ原則

補題が `lake build` を通しても、次に該当した時点で削除候補とする:

- フェーズ境界で誰からも参照されていない（`grep_search` で呼出 0）
- 同じ意味の補題がより簡潔に書き直された
- 上位補題が直接証明可能になり、経由する必要がなくなった

各フェーズ終了時に **「デッド補題レビュー」** を行い、候補をまとめて削除する。削除時は `git log` で経緯を残すのみ（アーカイブは保持しない）。

---

## 2. 新ディレクトリ構造

```
S2IL/Operations/
├── Gravity.lean                    # 公開 API facade（≤ 200 行）
└── Gravity/
    ├── Basic.lean                  # floating / settling の基本定義
    ├── Descent.lean                # landingDistance の意味論
    ├── Place.lean                  # placeFallingUnit / placeLDGroups
    ├── GroundingMono.lean          # 接地単調性
    ├── WaveStep.lean               # waveStep 定義と layer count 保存
    ├── ProcessWave.lean            # processWave 定義と終端性
    ├── Equivariance.lean           # CW 回転等変性（rotate180 は系として 1 行）
    └── Internal/                   # 外部から import しない
        ├── FloatUnits.lean
        ├── Place.lean              # foldl_placeFU 系の書込・保存補題
        └── Sort.lean               # mergeSort 関連
```

外部ファイル（Stacker など）は **`import S2IL.Operations.Gravity` のみ**を使う。`Internal/` 以下は `Gravity/` 配下からのみ参照可能とし、docstring で明記する。

---

## 3. 既存資産の再利用判定

既存の Gravity 層を「全廃棄」せず、次のフローで補題単位に判定する:

```
既存補題 L を評価
  │
  ├─ L が偽（反例あり）──────────→ 廃棄
  │
  ├─ L が真で、新構造の単一チェーンに収まる
  │     └─ そのまま移植（必要なら改名）
  │
  ├─ L が真だが、似た意味の別補題 L' が存在
  │     └─ L と L' を統合した 1 本に書き直す
  │
  └─ L が真だが誰にも使われない見込み
        └─ 廃棄（デッド補題候補）
```

### 3.1 再利用候補（Phase B 着手時に最終確認）

次は「真である可能性が高く、新構造でも同等の位置を占める」と見込まれるもの。移植時に改名・統合を検討する:

- `placeLDGroups_landing_groundingEdge_mono_step_generic` / `_step`（GroundedMono.lean）
- `foldl_placeFU_mixed_fixed_d_groundingEdge_mono`（GroundedMono.lean）
- `placeLDGroups_landing_nonEmpty`（CommExt/PlaceGrounding.lean）
- `floatingUnits_flatMap_positions_nodup` / `floatingUnits_positions_pairwise_disjoint`（CommExt/FloatUnits.lean）

### 3.2 廃棄確定（反例または設計上不要）

- 反例確定済みの scaffold 群（`landingDistance_foldl_placeFU_preserve_on_remaining` ほか）
- `_rotate180_comm` として独立証明されている補題群（§1.1 により系化）

---

## 4. 実施フェーズ

### Phase A: Archive（1 セッション）

**目的**: 既存 Gravity を非 build 状態に退避し、空 facade でビルドを通す。

- 新ブランチ `greenfield/gravity-rewrite` を作成
- `S2IL/Operations/Gravity/` 以下を `S2IL/_archive/Gravity-pre-greenfield/` へ退避
- 下流（Stacker 等）の import を暫定コメントアウト
- `lake build` green を確認

### Phase B: Skeleton（2〜3 セッション）

**目的**: 新構造の公開 API を axiom で scaffold し、下流が import だけで再度ビルド可能になる状態を作る。

- `Gravity.lean` facade を作成
- 各 `Gravity/*.lean` に **§1.1 単一チェーン原則に従った** 公開 API を axiom で宣言
  - 各操作の `_rotateCW_comm` を axiom 化
  - `_rotate180_comm` は axiom にせず、CW 版からの系として theorem で定義
- 下流の import を新 facade 経由に書換
- `lake build` green、`sorry = 0`、axiom 数をスナップショット取得

### Phase C: De-axiomatization（多数セッション）

**着手順の目安**（低リスク → 高リスク）:

1. Basic / Descent / Place の構造的補題（定義展開・length 保存系）
2. Internal/Sort（Mathlib 既存の組立）
3. Equivariance: CW 等変性（既存資産の移植が効く）
4. GroundingMono の単純な単調性（B1〜B3a 相当）
5. Internal/Place の disjoint 性・書込位置・値保存系
6. GroundingMono の複雑な帰納（B3b 相当）
7. ProcessWave の終端性と `waveStep_ngs_strict_bound` 相当

**各補題の着手前**に:
- §1.3 に従って真偽検証
- `lean-proof-planning` skill でゴール形状を確認
- 反例が出たら signature を修正し再検証

### Phase D: デッド補題レビューと後片付け（1〜2 セッション）

§1.4 に従って各 Phase 末に**軽量レビュー**を実施し、Phase D で**総仕上げ**を行う:

- `grep_search` で参照 0 の補題を列挙
- 残っている axiom / sorry の全点検
- `_archive/` の削除または tag `pre-greenfield-yyyymmdd` を付与
- `MILESTONES.md` および `sorry-plan.json` を更新

---

## 5. リスクと mitigation

| リスク | mitigation |
|---|---|
| 下流が private 補題に依存していた | Phase A 前に `grep_search -r "import S2IL.Operations.Gravity\."` で全下流依存を洗い出す |
| 再構築中も Layer B-3b 相当が再び破綻 | Phase C-5 (Internal/Place の再設計) を Phase C-6 より先に完遂してから着手 |
| CW 等変性の主証明が難航 | 既存資産（`processWave_rotate180_comm` など）の証明構造を移植テンプレートとして使う。ただし rotate180 専用の中間補題は系化して捨てる |
| デッド補題の判断ミスで必要な補題を消す | フェーズ末レビューでは「削除候補」リストを作り、次フェーズ着手時に実際に必要かを再確認してから削除 |
| `_archive/` の読み込みでエージェントのコンテキストが溢れる | `_archive/` 以下は `symbol-map.jsonl` から除外し、調査時は明示的に指定されたファイルのみ読む |

---

## 6. 成功基準

- `lake build` green、`sorry = 0`、Gravity 関連 axiom = 0
- `Gravity.lean`（facade）≤ 200 行
- 各 `Gravity/*.lean` ≤ 500 行
- `Gravity/Internal/` は外部 import なし
- 等変性定理は各操作について CW 版 1 本のみが「実質的な証明」を持ち、180° / CCW 版は系として 1 行で定義されている
- デッド補題レビューを各フェーズで実施した記録が残る

---

## 7. 関連

| 参照先 | 用途 |
|---|---|
| [`MILESTONES.md`](MILESTONES.md) | 上位の最終目標 |
| [`docs/agent/proof-plan-current-focus-guide.md`](../agent/proof-plan-current-focus-guide.md) | 新規 sorry 着手時の手順 |
| [`docs/agent/proof-retreat-pivot-guide.md`](../agent/proof-retreat-pivot-guide.md) | 撤退判断基準 |
| [`.github/skills/lean-counterexample/SKILL.md`](../../.github/skills/lean-counterexample/SKILL.md) | 真偽検証 |
| [`S2IL/_agent/sorry-plan.json`](../../S2IL/_agent/sorry-plan.json) | sorry / axiom の最新状態 |
