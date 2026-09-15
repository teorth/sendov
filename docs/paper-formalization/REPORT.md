# 纸面成果形式化：最终报告

## 交付结论

**已完成此前取得完整本地证明的全部 92 项结果族的 Lean 形式化及验收。**
这些结果族来自 14 份本地报告/笔记；一个结果族可以包含成对不等式或有限实例，
并非声称只有 92 条原子定理。原来仅有数学组合说明的 21 项，也已补成实际
导出的 Lean 定理，不再以文字推论代替形式化。

- 本地分支：`formalize/paper-results-20260914`
- 工作树：`/home/v-zhouziyu/work/sendov-paper-formalization-20260914`
- 已验收 Lean 源码提交：`8e1b056a241e6a99af2e2029569dc92a334c1a6d`
- 原基线：`0a4e966c41e1287f92d305d3bad8e70c8c295dde`
- 未推送远程，未改原 BASE 工作树。

## 数学与生产接线

### 统一直接预算 D

`Sendov.PaperUniform.uniform_D` 对所有自然数 **m≥256**、全部 **0<a<1**、
闭域 **−1≤x≤1**，从实际 raw-polar 积分推出实际 beta 积分预算的严格上界。
没有把端点界、Taylor/Laplace 界或尾项估计放进最终定理假设，没有逐次数表。

`Sendov.PaperNearClosure.near_endpoint_D` 对所有 **m≥7**、
**m(1-a)≤2/5**，给出严格余量 **B−T>(1-a)/1000**。
旧的 h/3、h/5、h/80 余量、m≥512 时 T<3/5、较宽射线上的更强收敛率，
均独立保留。旧大次数 cutoff 也有明确形式化推论。

两条新路线已经由 `Interior → Conjecture → Solution` 真正消费：
- n=6、7：小次数 first-origin 路线及定量 J 范数余量；
- n≥257：全部半径使用 polar + first-origin；
- 8≤n≤256 的近端点区域：使用统一近端点 first-origin 路线。

独立证明值依赖检查确认新分支不消费 polynomial centroid identity、
second-origin 或旧不相容性定理。全局 Solution 仍有旧分支用于其余有限区域；
不能据此删除旧 endgame。两个最终公开定理的严格性、等号分类和假设不变。

### 其余取得成果

- 平均二次矩边界刚性，已接入 Rubinstein 与两个公开结论。
- 实根分裂多项式的带重数临界点结构、倒数平衡及所有实指数 r≥1 的直径矩界。
- 实际积分的有限 Taylor、两端估计、sharp Laplace、全域 polar 端点/log 界。
- 曲率修正 secant 及不含积分的充分 gate；未声称 gate 处处为正。
- 保留全部有限 H 端点的复数 centered 展开、优化系数界、完整 majorant C-budget。
- 所有保留的认证实例：m=100 centered 误差、五组共轭族、浮点伪反例的精确排除、
  旧 3h/5 余量、两个 secant 连续邻域及完整复 polar 非空见证、两个域反例。
- 21 项补充推论的公开接口，包括完整复 polar hierarchy、实际均值/方差链、
  原始所有射线边界与准确常数。

## 验收证据

`VERIFICATION.json` 与 `receipts.json` 记录真实执行：

- **97 个受影响模块完成编译**；
- **96 次独立 Lean kernel 重放通过**；
- 合计 **193 项检查，零失败**；
- `Sendov` 是纯 import 汇总文件，没有本地声明：已编译，其声明所在模块逐个重放。
  不将这记作一次虚构 kernel 成功，也不通过命名空间前缀重复重放整个库。
- 总验收入口 `tests/PaperAcceptance.lean` 核对 **243 个命名审计根**；
  传递公理均限于 `propext`、`Classical.choice`、`Quot.sound`。
- 10 个边界/最终契约与冻结基线的完整类型和 universe 记录一致。
- 两个标准库生成器均实际重放；8 个输出逐字节不变。生成器只是见证产生器，
  数学正确性由相应 Lean 证明而非 Python 返回值保证。

成功编译/kernel 检查的记录用时合计约 **23.93 分钟**，不包含研究时间、
外层工具超时以及主动取消的重复命名空间重放。它不是整个任务的墙钟耗时。
本验收复用同一固定工具链的已验收依赖缓存；没有宣称重编或从空环境重放整个 Mathlib。

独立语义审阅分别检查了完整 D 与最终接线、精确实例的定义绑定、全部纸面清单。
来源审阅和父代理编译/kernel 证据在账本中分开记录。

## 实际效果与成本

相对基线，生产 Lean 从 **8,350 行增至 16,237 行**，净增 **7,887 行**；
测试/审计从 **1,222 行增至 10,818 行**，净增 **9,596 行**。
边界生产文件仍保留此前 **306→292 行**的局部缩短。

97 个验收模块的主 `.olean` 合计约 **181.22 MiB**，不包括 Mathlib 等依赖、
`.ilean` 或辅助文件。源码及对象计量见 `METRICS.json`。

缓存依赖下每模块重复三次的编译中位数：
- Interior：基线 **3.50 秒**，候选 **7.37 秒**；
- Conjecture：**3.66 秒 → 3.70 秒**；
- Solution：**2.85 秒 → 2.81 秒**。

这是共享主机上的有限测量，不是控制负载后的基准，也不是全 DAG 编译时间。
**当前收益是形式化覆盖、定量结论和可复用接口增强，不是全库压缩或加速。**
旧全域路线尚有消费者，新旧证明并存带来真实成本；未把新增行数或编译通过包装成优化。

## 明确未声称的事项

`SCOPE.md` 给出完整边界与对旧证据标签的纠正：
- 全部 m≥7、所有半径的 D 仍未在这项研究中证明；有限剩余域仍由旧路线覆盖。
- 全域 C-near 的几何前提尚不能推出其预算；这里只形式化已经取得的条件定理。
- AS01、AS02、AS04 三组旧渐近展开/收敛计算没有完整余项、根反演或收敛证明，
  明确保留为待证诊断，不算入 92 项已得证明。
- 不把全部下载的第三方论文、复共线搬运及一般共线等号分类算作已完成本地成果。

## 重放

当前机器已准备好固定环境与私有对象目录。完整串行重放：

```sh
python3 scripts/verify_paper_results.py \
  --config /home/v-zhouziyu/work/sendov-research-20260914-research/environment/config.json \
  --tag replay-new
```

中断后使用同一 tag 加 `--resume`；已记录成功且源码/配置未变的检查不重跑。
环境 JSON 指定固定 Lean、package cache 与项目 options。移到另一台机器时须提供
该机器相同工具链/依赖的环境配置，并准备私有项目对象；脚本不下载依赖或修改共享缓存。
生成见证可运行 `scripts/generate_centered_hundred.py` 与
`tests/generate_conjugate_budgets.py`。

入口索引：`ACCEPTANCE.json`、`SCOPE.md`、`VERIFICATION.json`、`METRICS.json`、
`receipts.json`、`axioms.json`、`modules.json`。
