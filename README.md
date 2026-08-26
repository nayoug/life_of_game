# Conway's Game of Life in Lean 4

本项目用 Lean 4 与 Mathlib 形式化无限二维棋盘上的有限 Conway 生命游戏图案。第二阶段已将第一阶段的可执行原型提升为有 soundness、搜索界内 completeness、证书最小性和实现 refinement 的认证分类器。


## 模型与性质

- 格子坐标是 `Int × Int`，世界是有限集 `Finset Cell`。
- `next w` 实现 B3/S23 单步规则，`evolve n w` 计算第 `n` 代。
- `IsRepeatingFrom` 表示非空状态的精确重复证书。
- `IsPeriodicFrom` 额外要求周期至少为 2，且重复起点不是静止状态。
- `IsSpaceshipFrom w start period delta` 要求 `evolve start w` 非空、周期为正、位移非零，并在一个周期后整体平移。

已证明最终消亡与最终静止、非平凡周期、飞船互斥。特别地，先消亡的非空图案不能利用空世界在任意平移下不变这一事实伪装成飞船，`singleton_not_eventuallySpaceship` 是对应的回归定理。

规范化现在是严格的平移等价判定：

```lean
normalize a = normalize b ↔ ∃ delta, b = translate delta a
```

`TranslationEquivalent` 已证明为自反、对称、传递关系；同时，非空有限世界若在某次平移后保持完全相等，则位移只能是 `(0, 0)`。

## 分类器

```lean
classify? 5 transientGlider
detect? 4 lightweightSpaceship
detectFast? 4 lightweightSpaceship
```

`classify? fuel w` 返回 `still`、`periodic`、`spaceship`、`extinct` 之一，或返回 `none`。`Detection` 使用四个构造器：

```lean
extinct start
still start
periodic start period
spaceship start period delta
```

因此缺少周期或位移等非法证书不能被构造。`detectVerified?` 可将普通执行结果包装为带 `DetectionValid` 证明的证书。

分类优先级为消亡、静止、周期、飞船。通用搜索器 `findUpTo?` 和 `findSomeUpTo?` 已证明：

- 返回值满足谓词且不超过 `fuel`；
- 界内存在命中项时一定返回某个证书；
- 返回的是第一个命中项。

四类具体搜索器继承相应的界内完备性。嵌套搜索按字典序最小化：先选择最小 `start`，再对该起点选择最小 `period`，不声称得到所有起点中的全局最小周期。顶层的 `detect_spaceship_complete` 明确带有前三个高优先级分支未命中的前提。

## 缓存实现

`orbit fuel w` 一次生成：

```text
[w, next w, ..., evolve fuel w]
```

定理 `orbit_length` 和 `orbit_get?` 分别验证轨道长度与每个界内索引。`detectFast?` 只从这条轨道读取状态，避免规格分类器重复从初始世界演化；核心精化定理为：

```lean
detectFast_eq_detectSpec :
  detectFast? fuel w = detectSpec? fuel w
```

所以缓存实现与易读规格实现逐输入返回完全相同的证书，并通过 `detectFast_sound` 继承正确性。

## 已验证样例

| 图案 | 结果 | 最小搜索证书 |
|---|---|---|
| `block` | 静止 | 起点 0 |
| `blinker` | 周期 | 起点 0，周期 2 |
| `glider` | 飞船 | 起点 0，周期 4，位移 `(1, 1)` |
| `singleton` | 消亡 | 第 1 代为空 |
| `twoStepExtinction` | 暂态后消亡 | 第 2 代为空 |
| `transientBlinker` | 暂态后周期 | 起点 1，周期 2 |
| `transientGlider` | 暂态后飞船 | 起点 1，周期 4，位移 `(1, 1)` |
| `lightweightSpaceship` | 非 glider 飞船 | 起点 0，周期 4，位移 `(-2, 0)` |

样例同时覆盖低 `fuel` 返回 `none`、提高 `fuel` 后成功，以及规格/快速实现结果一致。

## 完备性边界

所有 completeness 都是搜索界内的结论。`fuel` 不是任意生命游戏图案的停机界；`none` 只表示在当前边界内尚未找到证书，不表示第五种行为。项目不声称分类无限增长图案，也不解决任意有限初态的停机问题。
