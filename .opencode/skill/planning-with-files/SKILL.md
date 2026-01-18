---
name: planning-with-files
version: "2.1.2"
description: 实现 Manus 风格的基于文件的复杂任务规划。创建 task_plan.md、findings.md 和 progress.md。用于开始复杂的多步骤任务、研究项目或任何需要 >5 次工具调用的任务。
user-invocable: true
allowed-tools:
  - Read
  - Write
  - Edit
  - Bash
  - Glob
  - Grep
  - WebFetch
  - WebSearch
hooks:
  SessionStart:
    - hooks:
        - type: command
          command: "echo '[planning-with-files] 就绪。自动激活复杂任务，或使用 /planning-with-files 手动调用'"
  PreToolUse:
    - matcher: "Write|Edit|Bash"
      hooks:
        - type: command
          command: "cat task_plan.md 2>/dev/null | head -30 || true"
  PostToolUse:
    - matcher: "Write|Edit"
      hooks:
        - type: command
          command: "echo '[planning-with-files] 文件已更新。如果完成某个阶段，请更新 task_plan.md 状态。'"
  Stop:
    - hooks:
        - type: command
          command: "${CLAUDE_PLUGIN_ROOT}/scripts/check-complete.sh"
---

# 使用文件进行规划

像 Manus 一样工作：使用持久的 markdown 文件作为你的"磁盘工作记忆"。

## 重要：文件存储位置

使用此技能时：

- **模板** 存储在技能目录 `${CLAUDE_PLUGIN_ROOT}/templates/`
- **你的规划文件**（`task_plan.md`、`findings.md`、`progress.md`）应在**你的项目目录**中创建 — 即你正在工作的文件夹

| 位置 | 存放内容 |
|----------|-----------------|
| 技能目录（`${CLAUDE_PLUGIN_ROOT}/`）| 模板、脚本、参考文档 |
| 你的项目目录 | `task_plan.md`、`findings.md`、`progress.md` |

这确保你的规划文件与代码共存，而不是埋在技能安装文件夹中。

## 快速开始

在任何复杂任务之前：

1. **在项目中创建 `task_plan.md`** — 参考 [templates/task_plan.md](templates/task_plan.md)
2. **在项目中创建 `findings.md`** — 参考 [templates/findings.md](templates/findings.md)
3. **在项目中创建 `progress.md`** — 参考 [templates/progress.md](templates/progress.md)
4. **做决定前重读计划** — 刷新注意力窗口中的目标
5. **每个阶段后更新** — 标记完成、记录错误

> **注意：** 所有三个规划文件都应在当前工作目录（项目根目录）中创建，而不是在技能的安装文件夹中。

## 核心模式

```
上下文窗口 = RAM（易失、有限）
文件系统 = 磁盘（持久、无限）

→ 任何重要内容都写入磁盘。
```

## 文件用途

| 文件 | 用途 | 更新时机 |
|------|---------|----------------|
| `task_plan.md` | 阶段、进度、决策 | 每个阶段后 |
| `findings.md` | 研究、发现 | 任何发现后 |
| `progress.md` | 会话日志、测试结果 | 整个会话中 |

## 关键规则

### 1. 先创建计划
没有 `task_plan.md` 绝不要开始复杂任务。不可商量。

### 2. 两操作规则
> "每次 2 次查看/浏览器/搜索操作后，立即将关键发现保存到文本文件。"

这防止视觉/多模态信息丢失。

### 3. 决定前阅读
做重大决定前，阅读计划文件。这保持目标在注意力窗口中。

### 4. 操作后更新
完成任何阶段后：
- 标记阶段状态：`in_progress` → `complete`
- 记录遇到的任何错误
- 注明创建/修改的文件

### 5. 记录所有错误
每个错误都写入计划文件。这建立知识库并防止重复。

```markdown
## 遇到的错误
| 错误 | 尝试 | 解决方案 |
|-------|---------|------------|
| FileNotFoundError | 1 | 创建默认配置 |
| API timeout | 2 | 添加重试逻辑 |
```

### 6. 永不重复失败
```
if action_failed:
    next_action != same_action
```
跟踪你尝试了什么。改变方法。

## 三次错误处理协议

```
尝试 1：诊断与修复
  → 仔细阅读错误
  → 识别根本原因
  → 应用针对性修复

尝试 2：替代方法
  → 仍有相同错误？尝试不同方法
  → 不同工具？不同库？
  → 永不重复完全相同的失败操作

尝试 3：更广泛重新思考
  → 质疑假设
  → 搜索解决方案
  → 考虑更新计划

3 次失败后：升级到用户
  → 解释尝试内容
  → 分享具体错误
  → 寻求指导
```

## 读写决策矩阵

| 情况 | 操作 | 原因 |
|-----------|--------|--------|
| 刚写入文件 | 不要读 | 内容仍在上下文中 |
| 查看图像/PDF | 立即写入发现 | 多模态→文本前丢失 |
| 浏览器返回数据 | 写入文件 | 屏幕截图不持久 |
| 开始新阶段 | 阅读计划/发现 | 上下文陈旧时重新定位 |
| 发生错误 | 阅读相关文件 | 需要当前状态来修复 |
| 间隔后恢复 | 阅读所有规划文件 | 恢复状态 |

## 五问题重启测试

如果能回答这些问题，你的上下文管理就很好了：

| 问题 | 答案来源 |
|----------|---------------|
| 我在哪？ | task_plan.md 中的当前阶段 |
| 我要去哪？ | 剩余阶段 |
| 目标是什么？ | 计划中的目标陈述 |
| 我学到了什么？ | findings.md |
| 我做了什么？ | progress.md |

## 何时使用此模式

**用于：**
- 多步骤任务（3+ 步）
- 研究任务
- 构建/创建项目
- 跨越多次工具调用的任务
- 任何需要组织的任务

**跳过：**
- 简单问题
- 单文件编辑
- 快速查找

## 模板

复制这些模板开始：

- [templates/task_plan.md](templates/task_plan.md) — 阶段跟踪
- [templates/findings.md](templates/findings.md) — 研究存储
- [templates/progress.md](templates/progress.md) — 会话日志

## 脚本

自动化的辅助脚本：

- `scripts/init-session.sh` — 初始化所有规划文件
- `scripts/check-complete.sh` — 验证所有阶段完成

## 高级主题

- **Manus 原则：** 见 [reference.md](reference.md)
- **真实示例：** 见 [examples.md](examples.md)

## 反模式

| 不要 | 相反应该 |
|-------|------------|
| 使用 TodoWrite 进行持久化 | 创建 task_plan.md 文件 |
| 陈述一次目标就忘记 | 决定前重读计划 |
| 隐藏错误并静默重试 | 将错误记录到计划文件 |
| 把所有内容塞入上下文 | 将大内容存储在文件中 |
| 立即开始执行 | 先创建计划文件 |
| 重复失败的操作 | 跟踪尝试，改变方法 |
| 在技能目录创建文件 | 在你的项目中创建文件 |
