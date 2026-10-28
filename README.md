# 点支式玻璃幕墙驳接爪受力反演软件 V1.0

面向**建筑幕墙检测**场景的桌面工程软件。通过在玻璃分格上布置少量应变 / 挠度测点，反推各驳接爪的实际受力状态，并生成可签认的检测报告。

> Python 桌面应用 · PyQt6 · 2026

## 解决的工程问题

点支式玻璃幕墙由驳接爪（蜘蛛爪）连接玻璃与主体结构。这类节点**安装完成后被玻璃完全遮挡**，无法直接粘贴应变片测量受力，只能通过有限的测点数据反推。

难点在于：**测点数量少于待求的未知力数量**，方程组欠定且病态，直接求解会得到剧烈震荡、物理上不成立的解。

## 核心算法

`MuskInversionSolver` 采用 **加权正则化 + SVD 截断** 求解：

1. **加权正则化（岭回归）**：在最小二乘目标中加入解范数惩罚项，抑制测量噪声被放大
   ```
   min ‖Ax - b‖² + λ‖x‖²
   ```
2. **SVD 截断**：对系数矩阵做奇异值分解，舍弃小于阈值（`1e-6`）的奇异值分量，避免病态方向上的误差爆炸
3. **融合求解**：正则化解与 SVD 解加权融合，输出稳定的受力分布

```python
# 1) 正则化求解：(AᵀA + λI) x = Aᵀb
def weighted_reg_solve(self, mat_A, vec_b, reg_weight=None):
    m, n = mat_A.shape
    weight = self.reg_weight if reg_weight is None else float(reg_weight)
    A_reg = mat_A.T @ mat_A + weight * np.eye(n)
    b_reg = mat_A.T @ vec_b
    try:
        return np.linalg.solve(A_reg, b_reg)
    except np.linalg.LinAlgError:                  # 矩阵奇异时退回最小二乘
        return np.linalg.lstsq(A_reg, b_reg, rcond=None)[0]

# 2) SVD 截断求伪逆：小于阈值的奇异值直接置零
def svd_identify(self, mat_A, vec_b):
    U, s, Vt = np.linalg.svd(mat_A, full_matrices=False)
    s_inv = np.zeros_like(s)
    for idx, sigma in enumerate(s):
        if sigma > self.svd_eps:
            s_inv[idx] = 1.0 / sigma
    return Vt.T @ (s_inv * (U.T @ vec_b))

# 3) 两解按权重融合（默认 w1=0.6、w2=0.4），再做物理约束校验
fuse = w1 * x1 + w2 * x2
```

## 功能模块

| 模块 | 说明 |
|---|---|
| 角色权限 | 管理员 / 工程师 / 访客三级权限 |
| 工程台账 | 工程 → 玻璃分格 → 驳接爪节点三级数据维护 |
| 测点录入 | 应变、挠度数据录入与合法性校验 |
| 受力反演 | 多爪耦合受力反演，结果自动落库 |
| 三维联动 | QtWebEngine 内嵌 three.js，2D 分格图与 3D 模型同步着色 |
| 报告导出 | PDF 报告生成、签认 |
| 证据链 | 反演结果生成 SHA256 摘要并打包封存，可校验 |
| 审计日志 | 全流程操作留痕 |

## 技术栈

- **界面**：PyQt6、QPainter 自绘控件（热力图、分格示意图、力矢量图、统计图表）
- **三维**：QtWebEngine + three.js
- **算法**：NumPy、SciPy（`lstsq`、`svd`、`griddata`）
- **存储**：SQLite
- **输出**：QtPrintSupport（PDF）

## 运行

```bash
pip install PyQt6 PyQt6-WebEngine numpy scipy
python "点支式玻璃幕墙驳接爪受力反演软件 V1.0.py"
```

> `scene.html` 与 `three.js` 需与主程序放在同一目录（三维视图依赖）。

## 说明

本项目为个人工程实践，开发过程中使用了 AI 编程工具辅助编码，架构设计、业务建模与功能验证由本人完成。
