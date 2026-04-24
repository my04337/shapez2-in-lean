# Layer A/B アーキテクチャ（Greenfield 正本）

- 作成日: 2026-04-24
- 最終更新: 2026-04-24
- ステータス: **アーキテクチャ策定フェーズ / 実装未着手**
- スコープ: S2IL Layer A（データ型・Kernel・純粋関数な加工操作）および Layer B（振る舞い系）のコード構造
- 位置付け: 本ドキュメントは **新構造の正本** である。具体的な実施手順は [layer-ab-rewrite-plan.md](layer-ab-rewrite-plan.md) を参照する

---

## 0. このドキュメントの目的

S2IL の Layer A/B をゼロベースで設計する際の **コード構造の拘束条件** を定める。個別の補題や証明手順ではなく、

- ディレクトリ構造
- 公開 API / 非公開 API の境界
- Facade の責務
- MECE 分割原則
- 命名とサイズ上限
- インデックスに依存しないエージェント運用

といった「どの Layer にも横断的に適用される設計規約」を扱う。本ドキュメントが更新されたら、[layer-ab-rewrite-plan.md](layer-ab-rewrite-plan.md) と [MILESTONES.md](MILESTONES.md) の該当箇所を必ず再確認する。

---

## 1. 設計原則

### 1.1 Facade 中心原則（公開 API の集約）

各名前空間につき `X.lean` ファイル 1 本を **facade** とし、そこに:

- すべての公開 `def` / `theorem` / `notation`
- 各公開 API の docstring（日本語、使用例つき）
- 「この module の目次」をコメントブロックで先頭に記載

を集約する。外部モジュール（別名前空間・Test・Layer C 以降）からの `import` は **facade のみ**に限定する。

facade の行数は **≤ 150 行** を硬い上限とする。超過しそうになった場合は:

1. 補助補題を `Internal/` に退避
2. 公開 API を見直して削減
3. それでも収まらなければ名前空間を分割（例: `Operations.Gravity` → `Operations.Gravity.Descent` を独立 facade に昇格）

のいずれかで対応する。facade を肥大化させない。

### 1.2 ディレクトリによる API 境界（Internal 原則）

各 facade `X.lean` には対応する `X/` ディレクトリがあり、次の構造を取る:

```
X.lean                  # facade（公開 API 集約、≤ 150 行）
X/
├── <公開部品>.lean       # facade から再エクスポートされる公開 API の実装
├── ...
└── Internal/
    └── <補助補題>.lean    # facade 経由でのみ到達可能な補助補題
```

**規約**:

- `X/Internal/` 以下は `X.lean` および `X/*.lean` からのみ `import` してよい
- 他の名前空間 / Test / Layer C 以降からの `X/Internal/` 直接 `import` は **禁止**
- `X/Internal/` 内の各ファイル冒頭に次の docstring を必須とする:

  ```lean
  /-!
  # Internal: <内容の 1 行要約>

  このファイルは `X` namespace の補助補題を集める。
  **外部モジュール（X.lean, X/*.lean 以外）からは import 禁止**。
  -/
  ```

- Lean の `private` 修飾子は file-private の範囲でのみ補助的に使う。API 境界の主手段はディレクトリ階層である。

### 1.3 MECE 分割原則

操作 / Kernel コンポーネントを構成するファイルは、次の 4 種類に分類する。層をまたぐ補題は書かない:

| カテゴリ | 数学的対象 | 例 |
|---|---|---|
| **Defs** | 純粋関数定義と構造的性質（length 保存、型レベル等式、場合分け）| `Operations/Gravity/Defs.lean` |
| **Behavior** | 時間発展・終端性・単調性・収束など Layer B 的性質 | `Operations/Gravity/Behavior.lean` |
| **Equivariance** | CW 回転との可換性（単一チェーン）| `Operations/Gravity/Equivariance.lean` |
| **Internal** | 上記 3 種を下支えする補助補題 | `Operations/Gravity/Internal/*.lean` |

- Layer A のみの操作（例: Rotator）は Behavior を持たない
- Layer B がある操作は Defs → Behavior → Equivariance の順序で依存する
- Defs が Behavior 固有の命題を含んではならない（逆も同様）

### 1.4 単一チェーン原則（等変性）

回転群 $\mathbb{Z}/4\mathbb{Z}$ は CW 回転 1 つから生成される。したがって各操作 `f` の等変性は **CW 回転との可換性 1 本だけ** を主証明とし、他の回転（180° / CCW）は機械的に導出する:

$$f(s.\mathrm{rotate180}) = f(s.\mathrm{rotateCW}.\mathrm{rotateCW}) = f(s).\mathrm{rotateCW}.\mathrm{rotateCW} = f(s).\mathrm{rotate180}$$

この書き換えには `Kernel/Internal/Rotate180Lemmas.lean` に集約する `rotate180_eq_rotateCW_rotateCW` などの系を使う。`f_rotate180_comm` / `f_rotateCCW_comm` は facade 内で 1 行の系として定義し、独自の帰納証明を持たせない。

**禁止事項**: 操作 `f` について `f_rotateCW_comm` と `f_rotate180_comm` にそれぞれ独立した帰納法・場合分け証明を書くこと。

#### 1.4.1 例外: E/W 参照操作

**cut / halfDestroy / swap / shatterOnCut / eastHalf / westHalf / combineHalves**
は「絶対方角 E/W」に依存する。CW 90° 回転は E/W 軸を N/S 軸へ写すため、
これらの操作は CW 等変性を持たない。

反例 (`Shape.cut`): `s = CgRgCrSr` (NE=Cg, SE=Rg, SW=Cr, NW=Sr) のとき
- `s.rotateCW.cut` の東半分 = `SrCg----`
- `(s.cut.1).rotateCW` = `--CgRg--`

これらの操作は **180° 回転下でのみ** 綺麗な等変性を持つ。180° 回転は E↔W を
入れ替えるため、出力タプルの成分も swap される:

$$s.\mathrm{rotate180}.\mathrm{cut} = (s.\mathrm{cut.2}.\mathrm{rotate180},\ s.\mathrm{cut.1}.\mathrm{rotate180})$$

**原則**: E/W 参照操作については `rotate180_comm` を primitive axiom として置き、
`rotateCW_comm` / `rotateCCW_comm` は成立しないため定義しない。
CCW_comm も CW 経由では導出できないため、必要になった時点で rotate180 と CW
を合成した独自の補題として整備する。

### 1.5 真偽検証先行原則

すべての補題・定理は、証明着手前に次のいずれかで **真と判明するまで signature を確定しない**:

1. `lean-theorem-checker` で有効な Shape に対する反例検索
2. REPL `#eval` / `plausible` によるランダム検証
3. 数学的導出（既存の真定理からの含意）

偽と判明した命題は即座に signature を修正し、再検証する。**scaffold として sorry を書く前に必ず検証する**。

### 1.6 デッド補題クリーンアップ原則

補題が `lake build` を通しても、次に該当した時点で **削除候補** とする:

- フェーズ境界で誰からも参照されていない（`grep_search` で呼出 0）
- 同じ意味の補題がより簡潔に書き直された
- 上位補題が直接証明可能になり、経由する必要がなくなった

各フェーズ末に「デッド補題レビュー」を行い、候補をまとめて削除する。削除経緯は `git log` のみで残す（コード内アーカイブは作らない）。

### 1.7 認知負荷制約（インデックス不要原則）

本アーキテクチャは、`symbol-map.jsonl` / `dep-graph-baseline.json` / `sig-digest/` / `route-map.json` / `query-playbook.json` のような **インデックス機構が存在しない前提** で設計する。エージェントが機械的インデックスなしでも低コストに探索できることを目標とする。

そのための具体的な拘束:

| 制約 | 値 |
|---|---|
| Facade 行数上限 | ≤ 150 行 |
| 一般ファイル行数上限 | ≤ 300 行 |
| Internal ファイル行数上限 | ≤ 300 行 |
| 1 ディレクトリ直下の `.lean` ファイル数 | ≤ 8 本（超過時はサブ namespace 化） |
| facade 冒頭の「目次」コメント | 必須 |
| `Internal/` docstring の「import 禁止」宣言 | 必須 |

残す補助情報:
- `S2IL/_agent/sorry-plan.json` — sorry の状態と依存
- `S2IL/_agent/sorry-goals.md` — sorry シグネチャ一覧（自動生成）
- `S2IL/_agent/sorry-cards/*.md` — 個別 sorry の作業ノート

---

## 2. ディレクトリ構造（完全版）

```
S2IL.lean                          # ルート facade（全 Layer 再エクスポート、≤ 50 行）

S2IL/
│   ── Layer A: データ型 ──
├── Shape.lean                     # Shape 型系 facade
├── Shape/
│   ├── Types.lean                 # Color/PartCode/Quarter/QuarterPos/Layer/Shape 型
│   ├── GameConfig.lean
│   ├── Arbitrary.lean             # Plausible インスタンス
│   ├── Notation.lean              # Shape Code parse/serialize 公開 API + round-trip 定理
│   └── Internal/
│       ├── Parse.lean             # パーサ実装
│       └── Serialize.lean
│
│   ── Layer A: カーネル ──
├── Kernel.lean                    # Kernel facade
├── Kernel/
│   ├── BFS.lean                   # genericBFS 公開 API + 完全性定理
│   ├── Bond.lean                  # CrystalBond 公開 API
│   ├── Transform.lean             # rotateCW / rotate180 / rotateCCW 公開 API
│   └── Internal/
│       ├── BFSImpl.lean           # visitOrder / queue 実装
│       ├── BondImpl.lean
│       └── Rotate180Lemmas.lean   # rotate180 = rotateCW ∘ rotateCW など書換系
│
│   ── Layer A: ワイヤー系（スケルトン） ──
├── Wires.lean                     # Wires facade（A-3）
├── Wires/
│   ├── Signal.lean                # A-3-1
│   ├── Gates.lean                 # A-3-2
│   ├── Elements.lean              # A-3-3 / A-3-4
│   └── Internal/
│
│   ── Layer A / B: 加工操作 ──
├── Operations.lean                # 全操作 facade（Layer C から参照される唯一の入口）
├── Operations/
│   ├── Common.lean                # 操作共通ユーティリティ（公開）
│   ├── HalfDestroyer.lean         # A-2-1
│   ├── Cutter.lean                # A-2-1 + B-4-2
│   ├── Swapper.lean               # A-2-1 + B-4-3
│   ├── Rotator.lean               # A-2-2
│   ├── Painter.lean               # A-2-3
│   ├── ColorMixer.lean            # A-2-3
│   ├── CrystalGenerator.lean      # A-2-6
│   ├── Stacker.lean               # A-2-4 + B-4-1
│   ├── PinPusher.lean             # A-2-5 + B-4-4
│   ├── Gravity.lean               # B-1（落下 + 終端性 + CW 等変性）
│   ├── Shatter.lean               # B-2
│   ├── Settled.lean               # B-3
│   └── <Op>/                      # 操作ごとに同一構造
│       ├── Defs.lean              # 純粋関数定義（Layer A）
│       ├── Behavior.lean          # 振る舞い系（Layer B、該当操作のみ）
│       ├── Equivariance.lean      # CW 等変性本体
│       └── Internal/
│           └── *.lean             # 補助補題（外部 import 禁止）
│
│   ── Layer A / B: Machine ──
├── Machine.lean                   # Machine facade
└── Machine/
    ├── <機構別>.lean
    └── Internal/

Test/
├── Shape/                         # Layer A: 型 + round-trip
├── Kernel/                        # Layer A: BFS / Bond / Transform
├── Operations/                    # 純粋関数の代表値テスト
├── Behavior/                      # Layer B: 等変性・終端性
│   ├── Gravity.lean
│   ├── Shatter.lean
│   ├── Settled.lean
│   ├── Stacker.lean
│   ├── Cutter.lean
│   ├── Swapper.lean
│   └── PinPusher.lean
└── Machine/
```

### 2.1 名前空間と MILESTONES との対応

| ディレクトリ | MILESTONES の項目 | Layer |
|---|---|---|
| `Shape/` | A-1 | A |
| `Kernel/` | —（基盤）| A |
| `Wires/` | A-3 | A |
| `Operations/*.lean` の Defs 部 | A-2 | A |
| `Operations/*.lean` の Behavior 部 | B-1〜B-4 | B |
| `Operations/*/Equivariance.lean` | B-5 | B |
| `Machine/` | A-2 の統合 | A / B |

### 2.2 import ルール

- 外部から import してよいのは **facade (`S2IL.X` / `S2IL.X.Y`) のみ**
- `S2IL.X.Internal.*` はその namespace の owner 以外から import 禁止
- 循環防止のため Layer A → B → C → D の方向にのみ依存させる

---

## 3. Facade 規約

### 3.1 Facade 冒頭の目次

各 facade は次の形式のコメントブロックをファイル冒頭に持つ:

```lean
/-!
# <名前空間の要約>

## 公開 API

- `def foo` — 1 行説明
- `theorem foo_bar` — 1 行説明
- ...

## サブモジュール（公開）

- `S2IL.X.Y` — 役割
- `S2IL.X.Z` — 役割

## Internal（外部 import 禁止）

- `S2IL.X.Internal.*`
-/
```

この目次は docstring ではなくファイルレベルコメントとし、エージェントが `read_file` の先頭で全容を把握できるようにする。

### 3.2 Facade の内容

facade に置くもの:

- 公開 `def`（型シグネチャ + 短い定義または `X/` への委譲）
- 公開 `theorem`（主要定理 + 1 行系定義）
- 公開 `notation` / `instance`

facade に置かないもの:

- 帰納証明の本体（`X/<部品>.lean` または `X/Internal/` へ）
- 実装詳細の `def`
- Sanity test（`Test/` へ）

### 3.3 1 行系の書き方

等変性の 180° / CCW 版は facade に次のように書く:

```lean
/-- `gravity` は `rotate180` と可換（CW 版の系）。 -/
theorem gravity_rotate180_comm (s : Shape) :
    gravity (s.rotate180) = (gravity s).rotate180 := by
  simp only [rotate180_eq_rotateCW_rotateCW, gravity_rotateCW_comm]
```

系が 1 行で書けない場合、CW 版に問題があるとみなし再設計する（系のために新規補題を追加しない）。

---

## 4. Test 配置規約

- `Test/` 直下は Layer 別のサブディレクトリ（`Shape/` `Kernel/` `Operations/` `Behavior/` `Machine/`）に分ける
- 各テストファイルは対応する facade を 1 対 1 で import する
- `Internal/` を直接 import しない（API 境界の越境を防ぐ）
- Behavior テストは公開 API のみテストし、補助補題の単体テストは書かない

---

## 5. 命名規則（概要）

詳細は `docs/lean/naming-conventions.md` を参照。本ドキュメントでは構造的な規約のみを補強する:

- 等変性定理: `<operation>_rotate<CW|180|CCW>_comm`
- 終端性: `<operation>_terminates` もしくは `<operation>_WellFounded`
- 保存則: `<operation>_<preservedProperty>_preserved` / `<operation>_<property>_invariant`
- Internal 用の補助補題: 名前の衝突を避けるため namespace prefix（例: `Internal.FloatUnits.foldl_place_writes`）

---

## 6. 参照されなくなった場合の流儀

- 1 Phase 以上参照 0 のまま残っている補題は、次の Phase 着手時に削除判断する
- 削除は git で履歴を残し、コメントアウト / `_archive/` 化は行わない
- 再度必要になったら `git log -S` で復元する

---

## 7. 関連ドキュメント

| ファイル | 用途 |
|---|---|
| [layer-ab-rewrite-plan.md](layer-ab-rewrite-plan.md) | 本アーキテクチャを実装する Phase 別手順 |
| [MILESTONES.md](MILESTONES.md) | 上位の最終目標と Layer 定義 |
| [archive/gravity-greenfield-rewrite-plan.md](archive/gravity-greenfield-rewrite-plan.md) | 本アーキテクチャの前身（Gravity 限定）|
| [docs/lean/naming-conventions.md](../lean/naming-conventions.md) | Lean の命名規則 |
| [docs/agent/proof-plan-current-focus-guide.md](../agent/proof-plan-current-focus-guide.md) | 新規 sorry 着手時の手順 |
