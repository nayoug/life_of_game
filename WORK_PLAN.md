# Conway's Game of Life Lean 4 形式化项目工作计划

## 1. 项目目标

本项目使用 Lean 4 与 Mathlib，对 Conway's Game of Life（康威生命游戏）的有限初始图案进行建模、计算和证明。

第一阶段判断初始状态的以下四种**最终行为**：

1. **最终静止（eventually still）**：允许先经历有限步暂态，之后每一步都保持不变。
2. **最终成为飞船（eventually spaceship）**：允许先经历有限步暂态；之后形状按固定周期变化，并在每个周期后整体平移一个固定的非零位移。
3. **最终周期（eventually periodic）**：允许先经历有限步暂态；之后按固定周期变化，但不发生整体位移。
4. **最终消亡（eventually extinct）**：经过有限步后没有任何活细胞。

本文以后使用“飞船（spaceship）”，不再把整个类别称为“滑翔机（glider）”。标准五细胞滑翔机只是周期为 4、每周期对角移动一格的一种飞船。

项目需要同时满足两个目标：

- **可执行**：可以在 Lean 中运行分类函数，得到指定初始状态的分类结果。
- **可证明**：分类函数给出的结果有对应的 Lean 定理作为正确性保证，而不只是依赖 `#eval` 输出。

第一阶段不尝试解决任意有限图案的完全分类问题。生命游戏存在无限增长、永不重复和暂态极长等行为；对无限棋盘上的任意有限图案，不存在本项目可以依赖的通用有限停机界。因此分类函数必须允许返回“在给定搜索范围内尚未找到证书”。

---

## 2. 现有工程环境与集成方式

上级目录：

```text
D:\HuaweiMoveData\Users\joyce\Desktop\MyMathlibProject
```

已经配置：

- Lean：`v4.34.0-rc1`
- Mathlib：`v4.34.0-rc1`
- Lake 工程名：`MyMathlibProject`

本项目目录：

```text
D:\HuaweiMoveData\Users\joyce\Desktop\MyMathlibProject\life_of_game
```

实施时不在 `life_of_game` 中重复下载或初始化 Mathlib，而是复用上级目录的 `.lake` 和 `lake-manifest.json`。

已在上级 `lakefile.toml` 中增加一个独立库目标：

```toml
[[lean_lib]]
name = "LifeOfGame"
srcDir = "life_of_game"
```

这样源码仍全部位于当前目录内，同时可以从上级目录执行：

```powershell
lake build LifeOfGame
```

---

## 3. 范围与非目标

### 3.1 第一阶段支持范围

- 无限二维方格，而不是带边界的固定大小数组。
- 初始状态只包含有限个活细胞。
- 标准 Conway 规则 B3/S23：
  - 死细胞恰有 3 个活邻居时复活；
  - 活细胞有 2 或 3 个活邻居时存活；
  - 其他情况变为死细胞。
- 提供四个必须通过的标准样例：
  - 2×2 `block`：静止；
  - 五细胞 `glider`：飞船（周期 4，非零对角位移）；
  - 三细胞 `blinker`：周期为 2；
  - 单细胞 `singleton`：一步后消亡。
- 额外提供至少一个带暂态的样例，验证项目判断的是最终行为而不仅是初始形状。
- 分类失败时返回 `none`，不作错误判断。

### 3.2 第一阶段明确不做

- 不判定任意初始状态最终一定属于哪一类。
- 不支持无限活细胞集合。
- 不证明生命游戏的一般不可判定性结论。
- 不把所有飞船限制为标准五细胞滑翔机；只要搜索得到可靠的“周期 + 非零平移”证书，就可判定为飞船。
- 不开发图形界面。
- 不追求高性能大规模模拟。
- 不在第一阶段证明四种性质覆盖所有输入。

---

## 4. 数学模型设计

### 4.1 坐标与世界状态

坐标使用整数对：

```lean
abbrev Cell := Int × Int
abbrev World := Finset Cell
```

选择 `Int × Int` 的原因：

- 自然表达无限棋盘；
- 平移不受自然数下界限制；
- 飞船经过多次移动后无需处理数组越界；
- `Int` 与积类型已有可判定相等性，可用于 `Finset` 计算。

选择 `Finset Cell` 的原因：

- 本项目只处理有限活细胞集合；
- 可以执行成员判断、并集、过滤和计数；
- 状态相等可判定，适合 `decide`、`native_decide` 和分类函数。

### 4.2 八邻域

固定定义八个偏移量：

```lean
def neighborOffsets : Finset Cell
```

其元素为：

```text
(-1,-1), (-1,0), (-1,1),
( 0,-1),          ( 0,1),
( 1,-1), ( 1,0),  ( 1,1)
```

再定义：

```lean
def neighbors (c : Cell) : Finset Cell
def liveNeighborCount (w : World) (c : Cell) : Nat
```

应证明或计算验证：

- 每个格子恰有 8 个不同邻居；
- 格子本身不属于自己的邻域；
- 邻接关系对称；
- 活邻居计数不超过 8。

这些引理不是所有后续证明都必需，因此优先完成会被演化规格使用的部分，避免过早扩充理论。

### 4.3 候选格子与单步演化

下一步可能存活的格子一定是：

- 当前活细胞；或
- 当前活细胞的邻居。

因此定义有限候选集：

```lean
def candidates (w : World) : Finset Cell
```

然后用 Conway 规则过滤：

```lean
def survivesOrBorn (w : World) (c : Cell) : Bool
def next (w : World) : World
```

核心规格定理：

```lean
theorem mem_next_iff (w : World) (c : Cell) :
    c ∈ next w ↔
      liveNeighborCount w c = 3 ∨
      (c ∈ w ∧ liveNeighborCount w c = 2)
```

还应证明：

```lean
theorem next_empty : next ∅ = ∅
```

`mem_next_iff` 是模型正确性的中心定理。后面的样例证明既可以通过它逐点推导，也可以使用已证明等价关系后的可判定计算。

### 4.4 多步演化

定义：

```lean
def evolve : Nat → World → World
| 0,     w => w
| n + 1, w => evolve n (next w)
```

或者采用更方便证明组合律的参数顺序。需要建立：

```lean
theorem evolve_zero
theorem evolve_succ
theorem evolve_add
theorem evolve_empty
```

其中 `evolve_add` 用于周期与消亡性质的后续推理。

---

## 5. 四类最终行为的形式化定义

把“数学性质”“搜索得到的证书”和“用户看到的标签”分开。数学性质不含搜索上限；`fuel` 只属于算法层。

### 5.1 分类标签

```lean
inductive Status
| still
| spaceship
| periodic
| extinct
deriving Repr, DecidableEq
```

### 5.2 平移和飞船周期

先定义世界平移：

```lean
def translate (delta : Cell) (w : World) : World
```

飞船的核心不是某一种固定图案，而是两个时刻的状态只相差整体平移：

```lean
def IsSpaceshipFrom (w : World) (start period : Nat) (delta : Cell) : Prop :=
  w.Nonempty ∧
  0 < period ∧
  delta ≠ (0, 0) ∧
  evolve (start + period) w = translate delta (evolve start w)

def EventuallySpaceship (w : World) : Prop :=
  ∃ start period delta, IsSpaceshipFrom w start period delta
```

这正是“形状按周期变化，但整体一直平移”的可检验版本。必须证明：

```lean
theorem next_translate
theorem evolve_translate
theorem spaceship_repeats
```

其中 `spaceship_repeats` 从一次证书推出对任意 `k`：

```text
start + k * period 时的状态
= start 时的状态整体平移 k * delta
```

因此不需要无限观察“它一直平移”；一次有限证书，加上演化规则的确定性和平移不变性，就足以证明无限未来的规律。

空世界必须排除，否则空集在任意非零平移下仍等于自身，会被错误地判为飞船。

### 5.3 最终消亡

```lean
def EventuallyExtinct (w : World) : Prop :=
  ∃ start : Nat, evolve start w = ∅
```

由 `next_empty` 可进一步证明，一旦为空，之后永远为空。

### 5.4 最终静止

```lean
def EventuallyStill (w : World) : Prop :=
  ∃ start : Nat,
    (evolve start w).Nonempty ∧
    evolve (start + 1) w = evolve start w
```

这允许一个图案先演化若干步，最后变成静物。非空条件使其不与消亡重叠。

### 5.5 最终非平凡周期

```lean
def EventuallyPeriodic (w : World) : Prop :=
  ∃ start period : Nat,
    (evolve start w).Nonempty ∧
    2 ≤ period ∧
    evolve (start + period) w = evolve start w
```

周期至少为 2，从定义上排除静止。位移为零的重复属于周期，非零平移的重复属于飞船。

### 5.6 类别关系

对有限非空世界，应证明：若 `translate delta w = w`，则 `delta = (0, 0)`。这条有限集引理用于说明同一个重复证书不可能既有零位移又有非零位移。

“最终消亡”“最终非空静止”“最终非空周期/飞船”在确定性演化下也应证明必要的不相容性。若完整的两两互斥证明成本过高，第一阶段至少证明分类器分支所依赖的互斥事实，并通过固定优先级保证唯一输出。

---

## 6. 分类器设计

### 6.1 规范化：判断“形状相同”

对非空有限世界取左下角锚点，例如所有横坐标的最小值和所有纵坐标的最小值：

```lean
def anchor (w : World) (h : w.Nonempty) : Cell
def normalize (w : World) : World
```

`normalize w` 把锚点平移到 `(0, 0)`。需要证明：

```lean
theorem normalize_translate
theorem normalize_eq_iff_exists_translate
```

因此两个非空状态满足 `normalize a = normalize b`，当且仅当它们形状相同、只相差一个整体平移。锚点之差可以计算出实际位移 `delta`。

这个方法不限定图案必须是标准五细胞滑翔机，因此可以识别搜索范围内的其他飞船。

### 6.2 搜索轨道中的证书

计算有限轨道：

```lean
w, next w, evolve 2 w, ..., evolve fuel w
```

在每个新状态出现时检查：

1. 新状态为空：得到消亡证书 `start`。
2. 新状态和上一步完全相等且非空：得到最终静止证书。
3. 新状态和某个更早非空状态完全相等，间隔至少 2：得到最终周期证书 `(start, period)`。
4. 新状态和某个更早非空状态规范化后相等，但原状态不相等：得到飞船证书 `(start, period, delta)`。

这里比较轨道中的任意两个时刻 `i < j`，而不是只比较 `w` 和 `evolve j w`。这样能够识别先经历暂态、之后才进入稳定行为的初始状态。

### 6.3 对外接口

建议第一版接口：

```lean
def classify? (fuel : Nat) (w : World) : Option Status
```

其中：

- `some .still`：确认在 `fuel` 步内进入非空静止状态；
- `some .spaceship`：确认在 `fuel` 步内出现形状相同且位移非零的两个状态；
- `some .periodic`：确认在 `fuel` 步内进入周期至少为 2 的轨道；
- `some .extinct`：在 `fuel` 步内演化为空；
- `none`：搜索上限内尚未找到任何可靠证书；它不是第五种数学状态。

为了展示 Lean 证明得到的额外信息，建议同时提供详细接口：

```lean
structure Detection where
  status : Status
  start : Nat
  period : Option Nat
  displacement : Option Cell

def detect? (fuel : Nat) (w : World) : Option Detection
```

`classify?` 可以定义为 `detect?` 擦除证书字段后的简化视图。示例输出不仅告诉用户类别，还能显示“从第几步开始、周期多长、每周期移动多少”。

### 6.4 判断优先级

同一步搜索中建议按以下顺序解释证书：

1. 空状态返回 `.extinct`。
2. 相邻两个非空状态完全相等，返回 `.still`。
3. 两个非空状态完全相等且间隔至少为 2，返回 `.periodic`。
4. 两个状态规范化后相等且实际位移非零，返回 `.spaceship`。
5. 搜索结束仍无证书，返回 `none`。

该顺序使四个标签在实现层面保持清晰：

- 空世界优先视为消亡；
- 周期 1 单独视为静止；
- 零位移重复属于周期，非零位移重复属于飞船；
- 未知状态不被强制归类。

### 6.5 可执行程序与证明的连接

可以先写纯数据搜索函数，再为其结果证明 soundness；不建议一开始就让运行函数携带复杂的依赖证明对象。核心结构是：

```lean
def detect? : Nat → World → Option Detection

theorem detect_sound
    (h : detect? fuel w = some d) :
    DetectionValid w d
```

其中 `DetectionValid` 按 `status` 解释 `start`、`period` 和 `displacement`，并推出四种数学性质之一。

---

## 7. 正确性证明目标

### 7.1 单项 soundness

至少证明下面四个定理：

```lean
theorem classify_still_sound
    (h : classify? fuel w = some .still) : EventuallyStill w

theorem classify_spaceship_sound
    (h : classify? fuel w = some .spaceship) : EventuallySpaceship w

theorem classify_periodic_sound
    (h : classify? fuel w = some .periodic) : EventuallyPeriodic w

theorem classify_extinct_sound
    (h : classify? fuel w = some .extinct) : EventuallyExtinct w
```

这四个定理是第一阶段最重要的验收条件：分类器只要给出标签，该标签就必须符合形式化定义。

### 7.2 不要求的一般完备性

第一阶段不证明：

```lean
EventuallyPeriodic w → classify? fuel w = some .periodic
```

因为固定 `fuel` 可能小于“暂态长度 + 真实周期”。可以证明有界版本：如果两个构成证书的时刻都不超过 `fuel`，那么在排除更高优先级类别后分类器能够找到相应结果。

### 7.3 四个样例的完备结果

一般完备性虽然不要求，但必须对四个指定样例证明精确结果：

```lean
example : classify? 4 block = some .still := by native_decide
example : classify? 4 glider = some .spaceship := by native_decide
example : classify? 4 blinker = some .periodic := by native_decide
example : classify? 4 singleton = some .extinct := by native_decide
```

同时给出性质级定理：

```lean
theorem block_eventuallyStill : EventuallyStill block
theorem glider_eventuallySpaceship : EventuallySpaceship glider
theorem blinker_eventuallyPeriodic : EventuallyPeriodic blinker
theorem singleton_eventuallyExtinct : EventuallyExtinct singleton
```

样例的计算证明可以使用 `native_decide`，但核心通用定理不能全部退化为样例枚举。

---

## 8. 计划文件结构

```text
life_of_game/
├─ WORK_PLAN.md
├─ README.md
├─ LifeOfGame.lean
└─ LifeOfGame/
   ├─ Basic.lean
   ├─ Evolution.lean
   ├─ Translation.lean
   ├─ Normalization.lean
   ├─ Properties.lean
   ├─ Classifier.lean
   ├─ Patterns.lean
   └─ Examples.lean
```

各文件职责：

### `LifeOfGame/Basic.lean`

- `Cell`、`World`；
- 邻居偏移；
- 坐标加法和平移基础函数；
- 必要的 `Finset` 辅助引理。

### `LifeOfGame/Evolution.lean`

- `neighbors`；
- `liveNeighborCount`；
- `candidates`；
- `next`；
- `evolve`；
- `mem_next_iff`、`evolve_add` 等基础定理。

### `LifeOfGame/Translation.lean`

- 平移；
- 平移的组合性质；
- 演化对平移的不变性；
- 飞船规律可无限重复的通用定理。

### `LifeOfGame/Normalization.lean`

- 非空有限世界的锚点；
- 平移规范化；
- 规范化相等与“存在一个平移”之间的等价定理；
- 从两个锚点恢复实际位移。

### `LifeOfGame/Properties.lean`

- `Status`；
- `EventuallyStill`；
- `EventuallySpaceship`；
- `EventuallyPeriodic`；
- `EventuallyExtinct`；
- 类别之间必要的不重叠引理。

### `LifeOfGame/Classifier.lean`

- 有界步数搜索；
- 轨道历史和重复检测；
- `Detection` 与 `detect?`；
- `classify?`；
- 四个 soundness 定理；
- 对 `none` 语义的说明。

### `LifeOfGame/Patterns.lean`

- `block`；
- `glider`（作为飞船样例，而不是飞船定义）；
- `blinker`；
- `singleton`；
- 可选的未知样例，用来测试 `none`。

### `LifeOfGame/Examples.lean`

- 四个分类结果；
- 四个性质定理；
- `#eval` 演示；
- 回归测试。

### `LifeOfGame.lean`

- 汇总导入所有公开模块；
- 作为 `LifeOfGame` 库的入口。

---

## 9. 分阶段实施步骤

### 阶段 0：工程接入与最小编译验证

任务：

1. 在上级 `lakefile.toml` 增加 `LifeOfGame` 库目标。
2. 创建 `LifeOfGame.lean` 和一个最小模块。
3. 确认能够 `import Mathlib`。
4. 执行 `lake build LifeOfGame`。

验收：

- Lake 能找到当前目录下的模块；
- 不创建第二份 Mathlib 依赖；
- 上级已有 `MyMathlibProject` 库仍可正常构建。

### 阶段 1：世界、邻域和单步规则

任务：

1. 定义 `Cell` 和 `World`。
2. 定义八邻域和活邻居计数。
3. 构造有限候选集合。
4. 实现 `next`。
5. 证明 `mem_next_iff` 与 `next_empty`。
6. 用小图案做 `#eval` 冒烟测试。

验收：

- 单细胞下一步为空；
- 2×2 方块下一步不变；
- 核心成员关系定理通过编译。

### 阶段 2：多步演化与基础代数性质

任务：

1. 定义 `evolve`。
2. 证明零步、后继步和加法组合定理。
3. 证明空状态永久为空。
4. 定义世界平移。
5. 证明 `next` 和 `evolve` 与平移可交换。
6. 证明一次“周期后平移”的等式可以归纳推广到任意多个周期。

验收：

- `evolve 0 w = w`；
- `evolve (m+n) w` 可拆成两段演化；
- 对任意平移后的状态，先演化和先平移结果一致。

### 阶段 3：规范化与四类最终行为

任务：

1. 定义 `Status`。
2. 定义非空有限世界的 `anchor` 和 `normalize`。
3. 证明规范化判定平移等价。
4. 定义 `EventuallyStill`、`EventuallyPeriodic`、`EventuallySpaceship`、`EventuallyExtinct`。
5. 定义证书字段及其逻辑解释 `DetectionValid`。
6. 证明有限非空世界不可能在非零平移下保持完全相等。

验收：

- 性质定义无循环依赖；
- 空状态不属于最终静止、周期或飞船；
- 飞船定义不依赖某个硬编码图案；
- 一次飞船证书能够推出无限多个周期后的平移规律。

### 阶段 4：有界分类器

任务：

1. 实现 `extinctWithin`。
2. 生成长度至多为 `fuel + 1` 的有限轨道。
3. 实现轨道历史中的精确重复和规范化重复搜索。
4. 实现 `Detection`、`detect?` 和简化接口 `classify?`。
5. 检查小 `fuel`、零 `fuel` 和空输入的边界行为。

验收：

- 分类函数可执行；
- 所有循环显式按 `Nat` 递减，Lean 能确认终止；
- 无法确认的图案返回 `none`。

### 阶段 5：分类器 soundness 证明

任务：

1. 为每个布尔辅助判断建立真假反射引理。
2. 证明静止返回值可靠。
3. 证明飞船返回值可靠，并证明未来会继续按相同周期和位移运动。
4. 证明周期返回值可靠并提取周期见证。
5. 证明消亡返回值可靠并提取消亡步数。

验收：

- 四个 `classify_*_sound` 定理全部通过；
- 项目中没有 `sorry`、`admit` 或新增公理；
- `#print axioms` 显示关键定理只依赖预期的 Lean/Mathlib 公理基础。

### 阶段 6：标准样例与回归测试

任务：

1. 编码 `block`、`glider`、`blinker`、`singleton` 和一个带暂态样例。
2. 对每个样例运行分类器。
3. 对每个样例证明数学性质。
4. 加入至少一个返回 `none` 的输入，说明分类器不会强制分类。
5. 检查平移后的四个样例结果不受坐标原点影响。

验收：

| 初始状态 | 期望分类 | 最小检查步数 |
|---|---|---:|
| `block` | `still` | 1 |
| `glider` | `spaceship` | 4 |
| `blinker` | `periodic` | 2 |
| `singleton` | `extinct` | 1 |

### 阶段 7：文档和最终清理

任务：

1. 编写 `README.md`。
2. 说明坐标约定和图案表示方法。
3. 给出构建、求值和添加新图案的命令。
4. 明确 `fuel` 和 `none` 的含义。
5. 运行格式、构建和未完成证明检查。

验收：

- 新学习者可以按照 README 复现四个分类结果；
- 文档不宣称分类器对所有生命游戏状态完备；
- 所有公开定义名称和注释保持一致。

---

## 10. 测试与验证方案

从上级目录执行：

```powershell
lake build LifeOfGame
```

单独检查示例文件：

```powershell
lake env lean life_of_game\LifeOfGame\Examples.lean
```

搜索未完成证明：

```powershell
rg -n "\bsorry\b|\badmit\b" life_of_game
```

计算测试采用：

- `#eval`：展示人可读的分类结果；
- `example ... := by native_decide`：把结果纳入编译期回归测试；
- 普通定理证明：覆盖核心定义和分类器 soundness。

不能只把 `#eval` 输出当作形式化证明，因为输出本身不会建立一个可以被其他定理使用的命题。

---

## 11. 预期难点与处理策略

### 11.1 `Finset` 化简较繁琐

邻域、映射和平移会产生较多 `Finset` 成员关系证明。处理策略：

- 尽早建立 `mem_neighbors_iff`、`mem_translate_iff` 等局部规格引理；
- 后续证明使用这些规格引理，不直接反复展开实现；
- 样例级有限计算优先使用 `native_decide`。

### 11.2 平移规范化证明工作量较大

计算锚点容易，但证明“规范化相等当且仅当存在整体平移”需要处理 `Finset` 非空性和整数最小值。处理策略：

- 把 `anchor` 的输入限制为非空世界，避免给空集虚构最小值；
- 先证明平移如何改变锚点；
- 再由 `Finset.ext` 证明规范化定理；
- 搜索代码可为工程便利使用带默认值的可执行锚点，但定理层显式携带非空假设。

如果一次性证明双向等价成本过高，第一阶段至少证明分类器实际使用的方向：`normalize a = normalize b` 能构造出 `b = translate delta a`。

### 11.3 分类性质可能重叠

数学上静止状态也是周期为 1 的状态，空状态也会永久保持为空。处理策略：

- `EventuallyStill` 明确要求最终固定点非空；
- 最终静止明确要求非空，最终周期要求周期至少为 2；
- 精确相等解释为零位移周期，规范化相等但不精确相等解释为非零位移飞船；
- 分类器使用固定优先顺序；
- 对空输入明确返回 `.extinct`。

### 11.4 有界搜索不完备

`fuel` 太小时可能找不到消亡或周期。处理策略：

- 返回 `Option Status`；
- `none` 只表示“未确认”；
- soundness 定理不依赖完备性；
- 对指定样例选择足够的 `fuel`。

更重要的是，一旦找到重复，停止观察不是猜测：重复证书加上已经证明的演化性质，会严格推出无限未来行为。

### 11.5 编译期计算性能

候选集合会随图案扩大，朴素重复模拟可能较慢。第一阶段图案很小，先保持定义透明易证。只有实际出现构建性能问题时，才考虑缓存轨道、使用数组或优化候选集，避免过早优化破坏证明可读性。

---

## 12. 完成定义（Definition of Done）

满足以下所有条件时，第一阶段完成：

- [ ] 源码全部位于 `life_of_game` 目录中。
- [ ] 复用上级工程的 Lean 4 和 Mathlib 配置。
- [ ] `lake build LifeOfGame` 成功。
- [ ] 已实现无限棋盘上的有限活细胞模型。
- [ ] 已实现标准 B3/S23 单步和多步演化。
- [ ] 已证明 `mem_next_iff` 核心规格。
- [ ] 已形式化最终静止、最终飞船、最终周期、最终消亡四种性质。
- [ ] 已证明规范化相等能产生整体平移见证。
- [ ] 已证明一次飞船证书可推出以后任意多个周期的平移规律。
- [ ] 已实现返回 `Option Status` 的有界分类器。
- [ ] 已证明分类器四种成功返回值的 soundness。
- [ ] `block` 被分类为静止。
- [ ] `glider` 被分类为飞船，并返回周期 4 和非零位移。
- [ ] `blinker` 被分类为周期。
- [ ] `singleton` 被分类为消亡。
- [ ] 至少一个不支持的输入返回 `none`。
- [ ] 没有 `sorry`、`admit` 或项目自定义公理。
- [ ] README 包含构建、运行、定义和范围限制。

---

## 13. 推荐实施顺序总结

严格按以下依赖顺序推进：

```text
工程接入
  → 坐标与有限世界
  → 邻域与单步演化
  → 多步演化
  → 平移和规范化
  → 四类最终行为
  → 有界搜索辅助函数
  → 分类器
  → soundness 证明
  → 四个标准样例
  → README 与最终验收
```

每个阶段都应保持 `lake build LifeOfGame` 通过后再进入下一阶段。不要先堆积全部定义、最后一次性处理证明；对 Lean 项目而言，逐层建立稳定的规格引理会显著降低后续证明复杂度。

---

## 14. 第二阶段工作计划：从可靠原型到认证分类器

### 14.1 第二阶段定位

第一阶段已经完成以下主线：

- 无限棋盘上的有限活细胞模型；
- B3/S23 单步与多步演化；
- 平移、规范化和四类最终行为；
- 带 `fuel` 的可执行分类器；
- 分类成功结果的 soundness 证明；
- 静止、飞船、周期、消亡和暂态样例；
- `lake build LifeOfGame` 构建通过。

第二阶段不以增加大量已知图案为主要目标，而是把第一阶段的“可靠原型”提升为：

> 规格严谨、搜索界内完备、证书结构合法、实现避免重复演化的认证分类器。

第二阶段仍保留有界搜索。目标不是为任意生命游戏图案找到通用停机准则，而是完善下面四层保证：

```text
成功结果一定正确                   soundness
搜索界内存在证书时能够找到         bounded completeness
返回的起点或周期具有最小性         minimality
高效实现与清晰的规格实现结果一致   refinement
```

### 14.2 首要修正：飞船定义的非空条件

当前 `IsSpaceshipFrom` 要求初始世界 `w.Nonempty`，但真正需要非空的是进入飞船阶段后的状态：

```lean
evolve start w
```

否则一个非空图案先消亡后，空世界满足任意平移不变：

```lean
translate delta ∅ = ∅
```

从而可能错误地满足数学层的飞船定义。分类器因为优先检查消亡而不会输出这个错误结果，但性质定义本身仍然不够严谨。

应改为：

```lean
def IsSpaceshipFrom
    (w : World) (start period : Nat) (delta : Cell) : Prop :=
  (evolve start w).Nonempty ∧
  0 < period ∧
  delta ≠ (0, 0) ∧
  evolve (start + period) w =
    translate delta (evolve start w)
```

修改后需要同步更新：

- `spaceship_repeats`；
- `spaceshipWitness_sound`；
- `DetectionValid`；
- `classify_spaceship_sound`；
- 标准滑翔机样例证明；
- README 中的数学定义说明。

必须加入防回归定理：

```lean
theorem singleton_not_eventuallySpaceship :
    ¬ EventuallySpaceship singleton
```

如果直接证明该具体定理过于依赖计算细节，可以先证明更一般的互斥定理，再将它应用于 `singleton`。

### 14.3 完善四类行为之间的关系

第一阶段主要证明“分类器返回标签意味着对应性质成立”。第二阶段应进一步研究这些性质是否互斥，以及分类优先级是否只是一种实现选择。

计划证明以下通用结论：

```lean
theorem eventuallyExtinct_not_eventuallyStill :
    EventuallyExtinct w → ¬ EventuallyStill w

theorem eventuallyExtinct_not_eventuallyPeriodic :
    EventuallyExtinct w → ¬ EventuallyPeriodic w

theorem eventuallyExtinct_not_eventuallySpaceship :
    EventuallyExtinct w → ¬ EventuallySpaceship w
```

还应证明有限非空图案不可能在非零平移下保持完全相等：

```lean
theorem translate_eq_self_imp_delta_zero
    (hw : w.Nonempty)
    (h : translate delta w = w) :
    delta = (0, 0)
```

这一定理说明：

- 精确重复对应零位移周期；
- 规范化后相等但状态不相等对应非零位移飞船；
- 同一个非空重复证书不会同时被解释成周期和飞船。

需要谨慎处理“最终静止”和“最终周期”的语义。当前周期定义要求周期至少为 2，但一个静止状态也满足任意更大的重复周期。因此仅限制 `2 ≤ period` 并不能在数学上排除静止。

第二阶段应在以下两种方案中选择一种并保持一致：

1. 把 `EventuallyPeriodic` 定义为存在最小周期 `period ≥ 2`，并要求在所有 `0 < q < period` 时不重复；
2. 保留现有重复定义，但把它命名为 `EventuallyRepeating`，另定义排除最终静止的 `EventuallyPeriodic`。

推荐第二种方案，因为“重复证书”和“用户分类标签”可以清楚分层，相关证明也更自然。

### 14.4 完成平移规范化理论

当前已经证明：

```lean
normalize a = normalize b →
  ∃ delta, b = translate delta a
```

第二阶段要完成反方向，建立真正的平移等价判定：

```lean
theorem normalize_translate (delta : Cell) (w : World) :
    normalize (translate delta w) = normalize w

theorem normalize_eq_iff_exists_translate (a b : World) :
    normalize a = normalize b ↔
      ∃ delta, b = translate delta a
```

建议进一步定义显式关系：

```lean
def TranslationEquivalent (a b : World) : Prop :=
  ∃ delta, b = translate delta a
```

并证明：

```lean
theorem translationEquivalent_refl
theorem translationEquivalent_symm
theorem translationEquivalent_trans
theorem translationEquivalent_iff_normalize_eq
```

由此，`normalize` 可以被严格解释为有限图案在平移等价关系下的规范代表，而不只是分类器中的一个计算技巧。

### 14.5 搜索辅助函数的界内完备性

第一阶段已有：

```lean
findUpTo? fuel p = some n → p n = true
```

即 soundness。第二阶段增加反向结论：

```lean
theorem findUpTo_complete
    (hn : n ≤ fuel)
    (hp : p n = true) :
    ∃ m, findUpTo? fuel p = some m
```

同样为 `findSomeUpTo?` 建立界内完备性。之后推广到具体搜索器：

```lean
theorem extinctStart_complete
theorem stillStart_complete
theorem periodicWitness_complete
theorem spaceshipWitness_complete
```

这些定理只要求证书涉及的最大时刻不超过 `fuel`。例如飞船有界证书需要：

```lean
start + period ≤ fuel
```

由于 `detect?` 有分类优先级，顶层完备性应写成带排除条件的形式：

```lean
theorem detect_spaceship_complete
    (hspaceship : 存在 fuel 范围内的飞船证书)
    (hnoExtinct : fuel 范围内没有消亡证书)
    (hnoStill : fuel 范围内没有静止证书)
    (hnoPeriodic : fuel 范围内没有精确周期证书) :
    ∃ d, detect? fuel w = some d ∧ d.status = .spaceship
```

这能准确表达：分类器会返回按优先级最先适用的类别，而不是笼统声称所有性质都映射到唯一标签。

### 14.6 证明搜索结果的最小性

当前 `findUpTo?` 的实现从 `0` 向上选择第一个命中项，但尚未形式化证明“第一个”。第二阶段增加：

```lean
theorem findUpTo_le_fuel
    (h : findUpTo? fuel p = some n) :
    n ≤ fuel

theorem findUpTo_minimal
    (h : findUpTo? fuel p = some n) :
    ∀ m < n, p m = false
```

进一步得到：

- `extinctStart?` 返回最早消亡代数；
- `stillStart?` 返回最早静止起点；
- 固定 `start` 时，`periodicPeriod?` 返回最小候选周期；
- 固定 `start` 时，`spaceshipPeriod?` 返回最小候选飞船周期。

需要注意，当前嵌套搜索先最小化 `start`，再最小化 `period`，采用的是字典序最小性。文档和定理应明确这一点，而不能含糊地称为“全局最小周期”。

### 14.7 重构证书数据类型

当前统一结构：

```lean
structure Detection where
  status : Status
  start : Nat
  period : Option Nat
  displacement : Option Cell
```

允许构造无意义的组合，例如飞船却没有周期和位移。虽然 `detect?` 不会产生这些组合，但 API 类型没有表达这个约束。

建议改为和类别同步的代数数据类型：

```lean
inductive Detection
| extinct (start : Nat)
| still (start : Nat)
| periodic (start period : Nat)
| spaceship (start period : Nat) (delta : Cell)
deriving Repr, DecidableEq
```

再定义投影函数：

```lean
def Detection.status : Detection → Status
def Detection.start : Detection → Nat
```

这样：

- 无效字段组合无法构造；
- 模式匹配与 `DetectionValid` 更直接；
- `classify?` 仍可通过映射 `Detection.status` 提供简化接口。

还可以提供定理层的已验证证书：

```lean
structure VerifiedDetection (w : World) where
  detection : Detection
  valid : DetectionValid w detection
```

不建议让高频执行路径直接返回含证明的依赖结构；更合适的是让 `detect?` 返回普通数据，再用 `detect_sound` 构造 `VerifiedDetection`。

### 14.8 一次性轨道计算与实现精化

当前搜索器会多次调用：

```lean
evolve start w
evolve (start + period) w
```

这些调用会反复从初始状态开始计算。随着 `fuel` 增大，重复工作明显增加。

第二阶段先定义一次性轨道：

```lean
def orbit (fuel : Nat) (w : World) : Array World
```

要求：

```lean
orbit fuel w = #[w, next w, ..., evolve fuel w]
```

核心规格定理：

```lean
theorem orbit_size :
    (orbit fuel w).size = fuel + 1

theorem orbit_get
    (h : n ≤ fuel) :
    (orbit fuel w)[n]'... = evolve n w
```

保留当前清晰但重复计算的实现作为规格版本：

```lean
def detectSpec? (fuel : Nat) (w : World) : Option Detection
```

新增基于缓存轨道的实现：

```lean
def detectFast? (fuel : Nat) (w : World) : Option Detection
```

最终证明：

```lean
theorem detectFast_eq_detectSpec :
    detectFast? fuel w = detectSpec? fuel w
```

这个 refinement 定理是第二阶段最能体现 Lean 特点的目标之一：不仅证明优化程序没有误报，还证明它和易读规格实现逐输入得到完全相同的结果。

如果数组索引证明使第一版工作量过大，可以先使用 `List World` 完成规格和正确性，再在性能确有需要时换成 `Array World`。

### 14.9 第二阶段新增样例

除第一阶段样例外，至少增加：

1. **暂态后消亡**：需要两步或更多步才为空。
2. **暂态后周期**：初始图案先丢失一些细胞，再进入 oscillator。
3. **暂态后成为飞船**：初始状态包含滑翔机和会很快消失的远离干扰细胞。
4. **非滑翔机飞船**：如轻量级飞船（LWSS）；用来证明分类器识别的是一般飞船定义，而不是硬编码 glider。
5. **低 fuel 返回 `none`、足够 fuel 成功**：展示有界完备性的实际意义。
6. **消亡不是飞船**：防止空状态平移导致规格回归。

示例应同时提供：

- `#eval detect? fuel pattern` 的可读输出；
- `native_decide` 回归测试；
- 至少一个性质级定理或由 soundness 自动得到的推论。

### 14.10 实施顺序

第二阶段按以下顺序进行，每一步保持构建通过：

```text
修复飞船非空条件
  → 修复并补充回归测试
  → 明确周期与重复的语义
  → 证明四类行为的关键互斥关系
  → 完成规范化与平移等价理论
  → 证明通用搜索函数的完备性和最小性
  → 推广到四类具体证书搜索
  → 重构 Detection 为合法状态数据类型
  → 实现 orbit 缓存
  → 实现 detectFast?
  → 证明 detectFast? = detectSpec?
  → 增加暂态与其他飞船样例
  → 更新 README 和最终验收
```

### 14.11 建议文件调整

保持现有模块边界，新增或调整：

```text
LifeOfGame/
├─ Properties.lean       # 修正规格、重复/周期区分、互斥性
├─ Normalization.lean    # 完整的平移等价理论
├─ Search.lean           # 可选：通用搜索的 soundness/completeness/minimality
├─ Orbit.lean            # 一次性轨道及索引规格
├─ Classifier.lean       # 规格分类器、证书、顶层定理
├─ FastClassifier.lean   # 快速分类器与 refinement 定理
├─ Patterns.lean         # 新增第二阶段图案
└─ Examples.lean         # 回归测试与演示
```

如果 `Search.lean` 或 `FastClassifier.lean` 内容很少，可以暂时保留在 `Classifier.lean` 中；只有在模块职责明显分离时再拆文件。

### 14.12 第二阶段验收标准

- [x] `IsSpaceshipFrom` 要求 `evolve start w` 非空。
- [x] 消亡状态不会在数学定义层被判为飞船。
- [x] 明确区分“重复证书”和“非平凡周期类别”。
- [x] 已证明消亡与其他三个非空最终行为的关键互斥性。
- [x] 已证明非空有限世界在非零平移下不可能等于自身。
- [x] 已证明 `normalize (translate delta w) = normalize w`。
- [x] 已证明规范化相等与平移等价的双向定理。
- [x] `findUpTo?` 和 `findSomeUpTo?` 具有 soundness、界内 completeness 和最小性定理。
- [x] 四个具体搜索器具有相应的界内完备性结论。
- [x] `Detection` 类型不再允许无效字段组合。
- [x] 已实现只生成一次演化序列的 `orbit`。
- [x] 已实现缓存轨道的快速分类器。
- [x] 已证明快速分类器与规格分类器结果一致。
- [x] 已加入暂态消亡、暂态周期、暂态飞船和至少一种非 glider 飞船样例。
- [x] 已验证低 `fuel` 失败、足够 `fuel` 成功的边界行为。
- [x] `lake build LifeOfGame` 成功。
- [x] 项目中没有 `sorry`、`admit` 或新增自定义公理。
- [x] README 已解释第二阶段新增保证和剩余的不完备性边界。

### 14.13 第二阶段非目标

- 不解决任意无限棋盘初始状态的完全分类或停机问题。
- 不承诺自动找到任意长暂态、任意大周期或无限增长模式。
- 不在本阶段实现图形界面。
- 不优先支持大型 RLE 图案库；RLE 输入可作为后续阶段。
- 不为性能牺牲规格清晰度；优化必须通过 refinement 定理连接到规格实现。
