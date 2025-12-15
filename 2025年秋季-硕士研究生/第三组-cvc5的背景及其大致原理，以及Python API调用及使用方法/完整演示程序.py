# cvc5_complete_final_demo.py
"""CVC5 完整演示程序"""

import cvc5
from cvc5 import Kind


def setup_solver(logic="QF_LIA"):
    """设置求解器基础配置"""
    solver = cvc5.Solver()
    solver.setLogic(logic)
    solver.setOption("produce-models", "true")
    return solver


def parse_bitvector(value_str):
    """解析位向量字符串"""
    if value_str.startswith('#b'):
        # 二进制格式：#b00001111
        binary_str = value_str[2:]
        return int(binary_str, 2)
    elif value_str.startswith('#x'):
        # 十六进制格式：#xff
        hex_str = value_str[2:]
        return int(hex_str, 16)
    else:
        # 十进制格式
        return int(value_str)


def parse_rational(value_str):
    """解析有理数字符串，如 '(/ 13 5)'"""
    if value_str.startswith('(/ '):
        # 格式: (/ numerator denominator)
        parts = value_str.strip('()/ ').split()
        if len(parts) == 2:
            numerator = int(parts[0])
            denominator = int(parts[1])
            return numerator / denominator
    # 如果是普通数字
    try:
        return float(value_str)
    except:
        return value_str


def basic_arithmetic_example():
    """示例 1：简单算术约束"""
    print("=" * 50)
    print("示例 1：简单算术约束")
    print("=" * 50)

    solver = setup_solver("QF_LIA")

    int_sort = solver.getIntegerSort()
    x = solver.mkConst(int_sort, "x")
    y = solver.mkConst(int_sort, "y")
    z = solver.mkConst(int_sort, "z")

    # 添加约束：x + y > z ∧ x > 0 ∧ y < 10 ∧ z = 5
    constraint1 = solver.mkTerm(Kind.GT,
                                solver.mkTerm(Kind.ADD, x, y), z)
    constraint2 = solver.mkTerm(Kind.GT, x, solver.mkInteger(0))
    constraint3 = solver.mkTerm(Kind.LT, y, solver.mkInteger(10))
    constraint4 = solver.mkTerm(Kind.EQUAL, z, solver.mkInteger(5))

    # 组合所有约束
    all_constraints = solver.mkTerm(Kind.AND, constraint1, constraint2, constraint3, constraint4)
    solver.assertFormula(all_constraints)

    result = solver.checkSat()

    if result.isSat():
        print("✅ 可满足")
        # 使用 getValue 获取变量值
        x_val = solver.getValue(x)
        y_val = solver.getValue(y)
        z_val = solver.getValue(z)
        print(f"   x = {x_val}")
        print(f"   y = {y_val}")
        print(f"   z = {z_val}")

        # 验证结果
        x_int = int(str(x_val))
        y_int = int(str(y_val))
        z_int = int(str(z_val))
        print(f"   验证: {x_int} + {y_int} = {x_int + y_int} > {z_int} = {x_int + y_int > z_int}")
        print(f"   验证: {x_int} > 0 = {x_int > 0}")
        print(f"   验证: {y_int} < 10 = {y_int < 10}")
        print(f"   验证: {z_int} = 5 = {z_int == 5}")
    else:
        print("❌ 不可满足")
    print()


def bitvector_example():
    """示例 2：位向量操作"""
    print("=" * 50)
    print("示例 2：位向量操作")
    print("=" * 50)

    solver = setup_solver("QF_BV")

    bv_sort = solver.mkBitVectorSort(8)
    a = solver.mkConst(bv_sort, "a")
    b = solver.mkConst(bv_sort, "b")

    # 约束：a & b = 0x0F 且 a | b = 0xFF
    and_constraint = solver.mkTerm(Kind.EQUAL,
                                   solver.mkTerm(Kind.BITVECTOR_AND, a, b),
                                   solver.mkBitVector(8, 0x0F))

    or_constraint = solver.mkTerm(Kind.EQUAL,
                                  solver.mkTerm(Kind.BITVECTOR_OR, a, b),
                                  solver.mkBitVector(8, 0xFF))

    solver.assertFormula(and_constraint)
    solver.assertFormula(or_constraint)

    result = solver.checkSat()

    if result.isSat():
        print("✅ 可满足")
        a_val = solver.getValue(a)
        b_val = solver.getValue(b)

        # 解析位向量值
        a_str = str(a_val)
        b_str = str(b_val)
        a_int = parse_bitvector(a_str)
        b_int = parse_bitvector(b_str)

        print(f"   a = {a_str} (十进制: {a_int}, 十六进制: {a_int:#04x})")
        print(f"   b = {b_str} (十进制: {b_int}, 十六进制: {b_int:#04x})")

        # 验证结果
        and_result = a_int & b_int
        or_result = a_int | b_int
        print(f"   验证: a & b = {and_result:#04x} (应为 0x0f)")
        print(f"   验证: a | b = {or_result:#04x} (应为 0xff)")
        print(f"   验证通过: {and_result == 0x0f and or_result == 0xff}")
    else:
        print("❌ 不可满足")
    print()


def array_example():
    """示例 3：数组理论"""
    print("=" * 50)
    print("示例 3：数组理论")
    print("=" * 50)

    solver = setup_solver("QF_AUFLIA")

    index_sort = solver.getIntegerSort()
    value_sort = solver.getIntegerSort()
    array_sort = solver.mkArraySort(index_sort, value_sort)

    arr = solver.mkConst(array_sort, "arr")
    i = solver.mkConst(index_sort, "i")
    j = solver.mkConst(index_sort, "j")

    # 约束：arr[i] = 10 ∧ arr[j] = 20 ∧ i = j
    constraint1 = solver.mkTerm(Kind.EQUAL,
                                solver.mkTerm(Kind.SELECT, arr, i),
                                solver.mkInteger(10))

    constraint2 = solver.mkTerm(Kind.EQUAL,
                                solver.mkTerm(Kind.SELECT, arr, j),
                                solver.mkInteger(20))

    constraint3 = solver.mkTerm(Kind.EQUAL, i, j)

    all_constraints = solver.mkTerm(Kind.AND, constraint1, constraint2, constraint3)
    solver.assertFormula(all_constraints)

    result = solver.checkSat()

    if result.isSat():
        print("❌ 可满足（这不应该发生，因为约束矛盾）")
        i_val = solver.getValue(i)
        j_val = solver.getValue(j)
        arr_i = solver.getValue(solver.mkTerm(Kind.SELECT, arr, i))
        arr_j = solver.getValue(solver.mkTerm(Kind.SELECT, arr, j))
        print(f"   i = {i_val}, j = {j_val}")
        print(f"   arr[i] = {arr_i}, arr[j] = {arr_j}")
    else:
        print("✅ 不可满足（符合预期，约束存在矛盾）")
    print()


def string_example():
    """示例 4：字符串操作"""
    print("=" * 50)
    print("示例 4：字符串操作")
    print("=" * 50)

    solver = cvc5.Solver()
    solver.setLogic("QF_S")
    solver.setOption("produce-models", "true")

    string_sort = solver.getStringSort()
    s1 = solver.mkConst(string_sort, "s1")
    s2 = solver.mkConst(string_sort, "s2")

    # 约束：s1 + s2 = "hello world" 且 s1 = "hello"
    constraint1 = solver.mkTerm(Kind.EQUAL,
                                solver.mkTerm(Kind.STRING_CONCAT, s1, s2),
                                solver.mkString("hello world"))

    constraint2 = solver.mkTerm(Kind.EQUAL,
                                s1, solver.mkString("hello"))

    solver.assertFormula(constraint1)
    solver.assertFormula(constraint2)

    result = solver.checkSat()

    if result.isSat():
        print("✅ 可满足")
        s1_val = solver.getValue(s1)
        s2_val = solver.getValue(s2)
        print(f"   s1 = {s1_val}")
        print(f"   s2 = {s2_val}")

        # 直接使用字符串值进行验证
        s1_str = str(s1_val).strip('"')  # 移除引号
        s2_str = str(s2_val).strip('"')  # 移除引号
        print(f"   验证: '{s1_str}' + '{s2_str}' = '{s1_str + s2_str}'")
        print(f"   目标: 'hello world'")
        print(f"   匹配: {s1_str + s2_str == 'hello world'}")
    else:
        print("❌ 不可满足")
    print()


def complex_equation_example():
    """示例 5：复杂方程组求解"""
    print("=" * 50)
    print("示例 5：复杂方程组求解")
    print("=" * 50)

    solver = setup_solver("QF_LIA")

    int_sort = solver.getIntegerSort()
    x = solver.mkConst(int_sort, "x")
    y = solver.mkConst(int_sort, "y")
    z = solver.mkConst(int_sort, "z")

    # 系统约束：2x + 3y - z = 10, x - y + 2z = 5, x + y + z = 15
    constraint1 = solver.mkTerm(Kind.EQUAL,
                                solver.mkTerm(Kind.ADD,
                                              solver.mkTerm(Kind.MULT, solver.mkInteger(2), x),
                                              solver.mkTerm(Kind.MULT, solver.mkInteger(3), y),
                                              solver.mkTerm(Kind.MULT, solver.mkInteger(-1), z)
                                              ),
                                solver.mkInteger(10))

    constraint2 = solver.mkTerm(Kind.EQUAL,
                                solver.mkTerm(Kind.ADD,
                                              x,
                                              solver.mkTerm(Kind.MULT, solver.mkInteger(-1), y),
                                              solver.mkTerm(Kind.MULT, solver.mkInteger(2), z)
                                              ),
                                solver.mkInteger(5))

    constraint3 = solver.mkTerm(Kind.EQUAL,
                                solver.mkTerm(Kind.ADD, x, y, z),
                                solver.mkInteger(15))

    # 所有变量为正数
    pos_x = solver.mkTerm(Kind.GT, x, solver.mkInteger(0))
    pos_y = solver.mkTerm(Kind.GT, y, solver.mkInteger(0))
    pos_z = solver.mkTerm(Kind.GT, z, solver.mkInteger(0))

    # 组合所有约束
    all_constraints = solver.mkTerm(Kind.AND, constraint1, constraint2, constraint3, pos_x, pos_y, pos_z)
    solver.assertFormula(all_constraints)

    result = solver.checkSat()

    if result.isSat():
        print("✅ 系统有解：")
        x_val = solver.getValue(x)
        y_val = solver.getValue(y)
        z_val = solver.getValue(z)

        x_int = int(str(x_val))
        y_int = int(str(y_val))
        z_int = int(str(z_val))

        print(f"   x = {x_int}")
        print(f"   y = {y_int}")
        print(f"   z = {z_int}")

        # 验证解
        print("\n   验证结果:")
        eq1 = 2 * x_int + 3 * y_int - z_int
        eq2 = x_int - y_int + 2 * z_int
        eq3 = x_int + y_int + z_int
        print(f"   2*{x_int} + 3*{y_int} - {z_int} = {eq1} (应为 10)")
        print(f"   {x_int} - {y_int} + 2*{z_int} = {eq2} (应为 5)")
        print(f"   {x_int} + {y_int} + {z_int} = {eq3} (应为 15)")
        print(f"   所有方程满足: {eq1 == 10 and eq2 == 5 and eq3 == 15}")
    else:
        print("❌ 系统无解")
        print("   说明：这个特定的整数方程组在正整数范围内无解")
    print()


def boolean_logic_example():
    """示例 6：布尔逻辑"""
    print("=" * 50)
    print("示例 6：布尔逻辑")
    print("=" * 50)

    solver = setup_solver("QF_LIA")

    # 布尔类型
    bool_sort = solver.getBooleanSort()
    b1 = solver.mkConst(bool_sort, "b1")
    b2 = solver.mkConst(bool_sort, "b2")
    b3 = solver.mkConst(bool_sort, "b3")

    # 整数类型
    int_sort = solver.getIntegerSort()
    x = solver.mkConst(int_sort, "x")

    # 复杂布尔表达式： (b1 ∧ b2) ∨ (¬b3 ∧ (x > 5))
    expr1 = solver.mkTerm(Kind.AND, b1, b2)
    expr2 = solver.mkTerm(Kind.AND,
                          solver.mkTerm(Kind.NOT, b3),
                          solver.mkTerm(Kind.GT, x, solver.mkInteger(5)))

    final_expr = solver.mkTerm(Kind.OR, expr1, expr2)

    solver.assertFormula(final_expr)
    solver.assertFormula(solver.mkTerm(Kind.GT, x, solver.mkInteger(0)))

    result = solver.checkSat()

    if result.isSat():
        print("✅ 可满足")
        b1_val = solver.getValue(b1)
        b2_val = solver.getValue(b2)
        b3_val = solver.getValue(b3)
        x_val = solver.getValue(x)
        print(f"   b1 = {b1_val}")
        print(f"   b2 = {b2_val}")
        print(f"   b3 = {b3_val}")
        print(f"   x = {x_val}")

        # 验证表达式
        b1_bool = str(b1_val) == "true"
        b2_bool = str(b2_val) == "true"
        b3_bool = str(b3_val) == "true"
        x_int = int(str(x_val))

        left_side = b1_bool and b2_bool
        right_side = (not b3_bool) and (x_int > 5)
        result_val = left_side or right_side

        print(f"   验证: ({b1_bool} ∧ {b2_bool}) ∨ (¬{b3_bool} ∧ ({x_int} > 5)) = {result_val}")
    else:
        print("❌ 不可满足")
    print()


def incremental_solving_example():
    """示例 7：增量求解"""
    print("=" * 50)
    print("示例 7：增量求解")
    print("=" * 50)

    solver = cvc5.Solver()
    solver.setOption("incremental", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("QF_LIA")

    int_sort = solver.getIntegerSort()
    x = solver.mkConst(int_sort, "x")
    y = solver.mkConst(int_sort, "y")

    # 第一组约束
    print("第一步：添加约束 x > 0, y < 10")
    solver.push()
    solver.assertFormula(solver.mkTerm(Kind.GT, x, solver.mkInteger(0)))
    solver.assertFormula(solver.mkTerm(Kind.LT, y, solver.mkInteger(10)))

    result1 = solver.checkSat()
    print(f"   结果: {result1}")

    if result1.isSat():
        x_val = solver.getValue(x)
        y_val = solver.getValue(y)
        print(f"   当前解: x = {x_val}, y = {y_val}")

    # 添加额外约束
    print("\n第二步：添加约束 x = y")
    solver.push()
    solver.assertFormula(solver.mkTerm(Kind.EQUAL, x, y))

    result2 = solver.checkSat()
    print(f"   结果: {result2}")

    if result2.isSat():
        x_val = solver.getValue(x)
        y_val = solver.getValue(y)
        print(f"   当前解: x = {x_val}, y = {y_val}")
    else:
        print("   无解（符合预期，因为 x=y 与 x>0, y<10 可能冲突）")

    # 回退到之前的状态
    print("\n第三步：回退到第一步的状态")
    solver.pop()

    result3 = solver.checkSat()
    print(f"   结果: {result3}")

    if result3.isSat():
        x_val = solver.getValue(x)
        y_val = solver.getValue(y)
        print(f"   当前解: x = {x_val}, y = {y_val}")
    print()


def linear_real_example():
    """示例 8：线性实数运算"""
    print("=" * 50)
    print("示例 8：线性实数运算")
    print("=" * 50)

    solver = cvc5.Solver()
    solver.setLogic("QF_LRA")  # 线性实数算术
    solver.setOption("produce-models", "true")

    real_sort = solver.getRealSort()
    x = solver.mkConst(real_sort, "x")
    y = solver.mkConst(real_sort, "y")

    # 线性约束：2x + 3y = 10, x - y = 1, x > 0, y > 0
    constraint1 = solver.mkTerm(Kind.EQUAL,
                                solver.mkTerm(Kind.ADD,
                                              solver.mkTerm(Kind.MULT, solver.mkReal(2), x),
                                              solver.mkTerm(Kind.MULT, solver.mkReal(3), y)
                                              ),
                                solver.mkReal(10))

    constraint2 = solver.mkTerm(Kind.EQUAL,
                                solver.mkTerm(Kind.SUB, x, y),
                                solver.mkReal(1))

    constraint3 = solver.mkTerm(Kind.GT, x, solver.mkReal(0))
    constraint4 = solver.mkTerm(Kind.GT, y, solver.mkReal(0))

    all_constraints = solver.mkTerm(Kind.AND, constraint1, constraint2, constraint3, constraint4)
    solver.assertFormula(all_constraints)

    result = solver.checkSat()

    if result.isSat():
        print("✅ 可满足")
        x_val = solver.getValue(x)
        y_val = solver.getValue(y)
        print(f"   x = {x_val}")
        print(f"   y = {y_val}")

        # 解析有理数格式
        x_float = parse_rational(str(x_val))
        y_float = parse_rational(str(y_val))

        print(f"   解析后: x ≈ {x_float}, y ≈ {y_float}")
        print(f"   验证: 2*{x_float} + 3*{y_float} = {2 * x_float + 3 * y_float} (应为 10)")
        print(f"   验证: {x_float} - {y_float} = {x_float - y_float} (应为 1)")
        print(f"   验证: {x_float} > 0 = {x_float > 0}")
        print(f"   验证: {y_float} > 0 = {y_float > 0}")
    else:
        print("❌ 不可满足")
    print()


def demonstration():
    """主演示函数"""
    print("🎯 CVC5 SMT 求解器完整演示 - 完全最终版")
    print("=" * 60)

    # 显示 CVC5 版本信息
    solver = cvc5.Solver()
    print(f"📚 CVC5 版本: {solver.getVersion()}")
    print()

    # 运行所有示例
    basic_arithmetic_example()
    bitvector_example()
    array_example()
    string_example()
    complex_equation_example()
    boolean_logic_example()
    incremental_solving_example()
    linear_real_example()

    print("=" * 60)
    print("🎉 所有示例演示完成！")
    print("\n📊 CVC5 功能演示总结：")
    print("  ✅ 整数算术约束 - 基本算术运算和约束求解")
    print("  ✅ 位向量操作 - 位级运算和验证")
    print("  ✅ 数组理论 - 数组读写操作和矛盾检测")
    print("  ✅ 字符串操作 - 字符串连接和匹配")
    print("  ✅ 复杂方程组 - 线性方程组求解")
    print("  ✅ 布尔逻辑 - 布尔表达式和混合约束")
    print("  ✅ 增量求解 - 推入弹出约束栈")
    print("  ✅ 实数运算 - 线性实数算术")
    print("\n💡 CVC5 应用场景：")
    print("  • 程序验证和形式化方法")
    print("  • 软件测试和符号执行")
    print("  • 硬件验证和电路设计")
    print("  • 人工智能和约束规划")
    print("  • 数学定理证明")
    print("\n🔧 技术要点：")
    print("  • 使用 getValue() 获取模型值")
    print("  • 设置 produce-models=true 启用模型生成")
    print("  • 针对不同理论设置相应的逻辑")
    print("  • 处理特殊格式（位向量、有理数等）")


if __name__ == "__main__":
    try:
        demonstration()
    except Exception as e:
        print(f"💥 程序执行出错: {e}")
        import traceback

        traceback.print_exc()