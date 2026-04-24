# Problem 089 - Buddy Allocator C++

**ACMOJ Problem ID**: 2199

## Table of Contents

- [Problem 089 - Buddy Allocator C++](#problem-089-buddy-allocator-c)
  - [Table of Contents](#table-of-contents)
  - [Introduction](#introduction)
    - [Background](#background)
  - [Assignment Description](#assignment-description)
    - [Grade Composition](#grade-composition)
  - [Assignment Requirements](#assignment-requirements)
    - [Input Format](#input-format)
    - [Output Format](#output-format)
    - [Samples](#samples)
    - [Data Constraints](#data-constraints)
  - [Per-Testcase Resource Limits](#per-testcase-resource-limits)
  - [Test Data](#test-data)
  - [Submission Requirements](#submission-requirements)
    - [Submission Format](#submission-format)
    - [Submission Guidelines](#submission-guidelines)
    - [Evaluation Notes](#evaluation-notes)
    - [Academic Integrity](#academic-integrity)

## Introduction

### Background

This problem tests algorithmic problem-solving skills.

## Assignment Description

### Grade Composition

| Grading Component | Percentage |
| :--: | :--: |
| Pass **2199. Buddy Allocator C++** | 80% |
| Code Review | 20% |

Here are several points that need clarification:

- In the Code Review, we will **strictly examine your code style and repository organization structure, etc.**

- This assignment provides some sample data for testing, stored in the `/workspace/data/089/data_test/` directory. Note that these are not the test cases on the Online Judge. Passing all local test cases does not guarantee that you will pass the OJ tests.

- Besides the provided sample data, we also encourage you to design your own test data based on your program logic to assist debugging.

## Assignment Requirements

### Problem Description

> 内核里可没有 STL 容器，所以请不要使用 STL 喵

请在 [attachment]2199-public.zip[/attachment] / [JBox](https://jbox.sjtu.edu.cn/l/Z1ecIu) 查看本题的完整题面与测试样例.

ACM 班的操作系统课程大作业是用 Rust 写一个微内核. 其中需要实现一个内存分配器来为操作系统管理内存, Conless 决定使用 Buddy Allocator 来实现. Buddy Allocator 是一种内存分配算法, 它将内存分割成大小为 2 的幂次方的块, 来高效应对不同的内存申请/释放需求.

Buddy Allocator 的原理是这样的:

<div align=center><image src="https://acm.sjtu.edu.cn/OnlineJudge/oj-images/48a5d6b4-a32a-47cd-94f6-d50458a0414e"></div>
<br>

假设总共有 $64$ 个 byte 的可用内存空间 (例如 0x00 - 0x3f), n内存的最小分配单元为 $4$ byte, 那么 buddy allocator 将这 $64$ 个 byte 的内存空间分割成大小为 $4$, $8$, $16$ 和 $32$ 的块, 产生
- $16$ 个 $4$ byte 的块, 分别对应内存地址 0x00 - 0x03, 0x04 - 0x07, ..., 0x3c - 0x3f
- $8$ 个 $8$ byte 的块, 分别对应内存地址 0x00 - 0x07, 0x08 - 0x0f, ..., 0x38 - 0x3f, 每个块 _包含_ 两个 $4$ byte 的块
- $4$ 个 $16$ byte 的块, 分别对应内存地址 0x00 - 0x0f, 0x10 - 0x1f, 0x20 - 0x2f, 0x30 - 0x3f, 每个块 _包含_ $2$ 个 $8$ byte 的块
- $2$ 个 $32$ byte 的块, 分别对应内存地址 0x00 - 0x1f, 0x20 - 0x3f, 每个块 _包含_ $2$ 个 $16$ byte 的块

如上图所示. 

在初始状态下, 只有最上层 (layer 3) 的两个块为空闲, 下层块由上层节点块分裂产生, 也可以合并重新产生上层节点. 每次内存申请操作以 2 的幂次为单位, allocator 前往对应的 layer 找空闲块, 如果对应位置不存在空闲块, 则向上层申请分裂. 释放内存时, 向对应 layer 的对应位置插入空闲块, 并尝试与兄弟节点合并重新产生上层节点.

上面的描述大概无法让你听懂, 所以请查看下发文件中的详细题面.

### 题目要求
不幸的是, Conless 要去出数据结构机考题, 所以只好把这一艰巨的任务交给你了. 出于仁慈, 他不准备让你们用 Rust 写, 而是用 C++ 实现其中的接口.

请实现一个基于 buddy allocator 算法 (允许进行魔改) 的内存分配器, 以可用内存大小 $ram\ size$ 与最小块大小 $min\ block\ size$ 初始化, 支持以下三种操作:

- `int malloc(int size)`: 申请大小为 $size$ 的内存块 (为了方便评测, 本题要求申请的内存块是以 $size$ 的**整数倍**为起点中**地址最小**的可用内存块, 即若 $size=8$, 当前可用内存为 $0-4, 16-63$, 则返回 $16$). 若成功分配, 返回申请的内存块的起始地址, 否则返回 `-1`.
- `int malloc_at(int addr, int size)`: 在 $addr$ 处申请大小为 $size$ 的内存块. 若成功分配, 返回 `addr`, 否则返回 `-1`.
- `void free_at(int addr, int size)`: 释放 $addr$ 处大小为 $size$ 的内存块. 保证该内存块一定由成功的申请操作得到.

### Input Format

请按上述要求完成下发文件中的 `src.hpp` 并提交.

### Output Format



### Samples

No sample data provided for this problem.

### Data Constraints

设总操作数为 $Q$.

可用内存地址均从 0 开始. 保证 $ram\ size$ 与 $size$ 均为 $min\ block\ size$ 乘以 2 的整数次幂, $addr$ 是 $size$ 的整数倍且小于 $ram\ size$. 除申请已经被申请过的内存区域外, 你不需要考虑任何非法操作 (例如 double free, 访问越界等).

对于 20% 的数据, 保证 $Q$ 与 $ram\ size$ 不大于 $100$.

对于 50% 的数据, 保证 $Q$ 与 $ram\ size$ 不大于 $5\times 10^3$.

对于 100% 的数据, 保证 $Q$ 与 $ram\ size$ 不大于 $3\times 10^5$, $min\ block\ size$ 的取值为 $1$, $2$ 或 $4$.

本题将在 50% 的测试数据上开启内存泄漏检查, 请确保你的程序是内存安全的. 你可以在本地使用 `valgrind` 进行自查.

## Per-Testcase Resource Limits

- **Time Limit (per test case)**: 1000 ms
- **Memory Limit (per test case)**: 512 MiB
- **Disk Usage**: No disk usage is permitted.

## Test Data

The test data for this problem is located at `/workspace/data/089/data_test/`.

Attachments and starter files for this problem are located at `/workspace/data/089/`.

## Submission Requirements

### Submission Format

Submit a single C++ source file to the Online Judge. The OJ provides its own `main.cpp` which `#include "src.hpp"`. Your submission will be written to `src.hpp` and compiled together with the OJ's driver code.

### Submission Guidelines

- The submitted code must be able to compile successfully through the above compilation process
- The program needs to be able to read data from standard input and write results to standard output
- Please ensure the code runs correctly within the given time and space limits
- **You must use C++ or C language** to implement this assignment

### Evaluation Notes

- The evaluation system will test your program using the provided test data
- The program output must exactly match the expected output (including format)
- Exceeding time or memory limits will be judged as the corresponding error type
- Please pay attention to the overall time performance of your code and the time complexity of each part of your algorithm.

### Academic Integrity

If any violations are found during evaluation or code review (including but not limited to using unconventional methods to pass test cases), your final score may be significantly reduced or become **0 points**.
