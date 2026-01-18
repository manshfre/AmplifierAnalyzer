from __future__ import annotations
import copy
import traceback
import itertools
import re
import math
from dataclasses import dataclass, field
from typing import Dict, List, Callable, Set, Optional, DefaultDict, Tuple, Any, Union
from collections import defaultdict
from enum import Enum, auto

# ------------------------------
# 核心电路分析器
# ------------------------------
# 假设偏置电路没有电流束
# 低压电流镜未考虑电阻
# 电流源路径的定义问题
# 未考虑电阻除频率补偿、共模检测外的子结构
# 未考虑电容除频率补偿、共模检测、滤波外的子结构
# RC相关频率补偿、共模检测、滤波基于预定义规则
# 默认级联管子与低压电流镜处在对称支路上(同时默认对称支路的管子参数一定相等)
class CircuitAnalyzer:
    """
    电路分析器 (CircuitAnalyzer)
    调用后可对电路的子结构进行分析、对参数进行精简、对初始解进行修改
    DeviceTags、CircuitPorts、SubStructureType、APPConfig是这个分析器的工具，代表这个分析器可以识别的器件标签、特殊端口名称、子结构类型、分析器数据接口格式。
    Device是该分析器识别到的器件、DeviceSub是器件所属子结构实例的引用
    Circuit是该分析器识别到的电路、CircuitSub是在Circuit中识别出的子结构实例
    子结构要先注册到SubStructureType中，才能被识别并登记到CircuitSub中与DeviceSub中
    """
    # ------------------------------
    # 1. 内部类定义
    # ------------------------------
    class AnalysisConfig:
        """
        [真理之源] AnalysisConfig
        定义全架构统一的常量键。替代原有的 DeviceTags 类及分散的字符串。
        
        功能：
        1. 提供所有架构层面的常量（Tags, Relations, Structures, Ports）。
        2. 提供属性的中文描述映射。
        3. 支持运行时动态添加/删除常量（用于扩展分析器能力）。
        """

        # =========================================================================
        # 1. 常量定义区 (Constants Definitions)
        # =========================================================================
        
        # --- A. 结构与分组 Keys (Structure & Group Keys) ---
        STR_DIFF_PAIR       = "DIFFERENTIAL_PAIR"      # 差分输入对
        STR_CASCODE         = "CASCODE"                # 级联

        STR_STD_MIRROR      = "STD_CURRENT_MIRROR"     # 普通电流镜

        STR_LV_MIRROR       = "LV_CURRENT_MIRROR"      # 低压电流镜
        STR_LV_MIRROR_PAIR  = "LV_MIRROR_PAIR"         # 低压镜像对

        STR_LOAD_TYPICAL    = "LOAD_TYPICAL"           # 典型负载
        STR_LOAD_A          = "LOAD_A"                 # A型负载
        STR_LOAD_B          = "LOAD_B"                 # B型负载
        STR_LOAD_C          = "LOAD_C"                 # C型负载

        STR_OUTPORT_PAIR    = "OUTPORT_PAIR"           # 输出端对
        STR_OUTPUT_PAIR     = "OUTPUT_PAIR"            # 输出对

        STR_CM_DETECT_A     = "COMMON_DETECT_A"        # 共模检测A (2管)
        STR_CM_DETECT_B     = "COMMON_DETECT_B"        # 共模检测B (4管)
        STR_RC_CM_DETECT    = "RC_COMMON_DETECT"       # RC共模检测

        STR_FREQ_COMPENSATE = "FREQ_COMPENSATE"        # 频率补偿
        STR_SYM_CAPACITOR   = "SYM_CAPACITOR"          # 对称电容

        STR_TAIL_INPUT      = "TAIL_CURRENT_INPUT"     # 输入尾电流源
        STR_TAIL_COMMON     = "TAIL_CURRENT_COMMON"    # 公共尾电流源
        STR_TAIL_OUTPUT     = "TAIL_CURRENT_OUTPUT"    # 输出尾电流源

        # --- B. 关系 Keys (Relation Keys) ---
        REL_CASCODE_M2S          = "CASCODE_MAIN_TO_SLAVE"  #描述主从级联关系

        REL_STD_REF2MIRROR       = "STD_REF_TO_MIRROR"      #描述普通电流镜参考管的镜像管
        REL_STD_REF2BIAS         = "STD_REF_TO_BIAS_MIRROR"     #描述普通电流镜参考管的偏置镜像管
        REL_STD_ROOT2BIAS        = "STD_ROOT_TO_BIAS_MIRROR"    #描述根参考管的偏置镜像管

        REL_LV_LREF2UREF         = "LV_LREF_TO_UREF"
        REL_LV_LREF2UBIAS        = "LV_LREF_TO_UBIAS"
        REL_LV_LREF2TOKEN        = "LV_LREF_TO_TOKEN"

        # --- C. 标签 Keys (Tag Keys) ---
        TAG_DIODE_MOS            = "DIODE_MOS"
        TAG_IN_CURRENT_BEAM      = "IN_CURRENT_BEAM"

        TAG_CASCODE_MAIN         = "CASCODE_MAIN"
        TAG_CASCODE_SLAVE        = "CASCODE_SLAVE"

        TAG_DIFF_POS             = "DIFF_POSITIVE"
        TAG_DIFF_NEG             = "DIFF_NEGATIVE"

        TAG_OUTPORT_POS          = "OUTPORT_POSITIVE"
        TAG_OUTPORT_NEG          = "OUTPORT_NEGATIVE"
        TAG_OUTPUT_POS           = "OUTPUT_POSITIVE"
        TAG_OUTPUT_NEG           = "OUTPUT_NEGATIVE"

        TAG_STD_MIRROR_REF       = "STD_MIRROR_REF"
        TAG_STD_MIRROR_MIRROR    = "STD_MIRROR_MIRROR"
        TAG_STD_MIRROR_BIAS      = "STD_MIRROR_BIAS"
        TAG_ROOT_REF             = "ROOT_REF"

        TAG_LV_UPPER_REF         = "LV_UPPER_REF"
        TAG_LV_LOWER_REF         = "LV_LOWER_REF"
        TAG_LV_UPPER_BIAS        = "LV_UPPER_BIAS"
        TAG_LV_UPPER_MIRROR      = "LV_UPPER_MIRROR"
        TAG_LV_LOWER_MIRROR      = "LV_LOWER_MIRROR"
        TAG_LV_BIAS_MIRROR       = "LV_BIAS_MIRROR"
        TAG_LV_PAIR              = "LV_MIRROR_PAIR"

        TAG_LOAD_TYP             = "LOAD_TYPICAL"
        TAG_LOAD_A_DIO           = "LOAD_A_DIODE"
        TAG_LOAD_A_TYP           = "LOAD_A_TYPICAL"
        TAG_LOAD_B               = "LOAD_B"
        TAG_LOAD_C               = "LOAD_C"

        TAG_CM_OUTER             = "CM_OUTER"
        TAG_CM_INNER             = "CM_INNER"
        TAG_CM_2MOS              = "CM_2MOS"
        TAG_CM_4MOS              = "CM_4MOS"

        TAG_COMPENSATE           = "COMPENSATE"
        TAG_RC_CM_DETECT         = "RC_CM_DETECT"
        TAG_SYM_CAPACITOR        = "SYM_CAPACITOR"

        # --- D. 端口 Keys (Port Keys) ---
        PORT_POWER_POS           = "POWER_POSITIVE"
        PORT_POWER_NEG           = "POWER_NEGATIVE"
        PORT_INPUT_POS           = "INPUT_POSITIVE"
        PORT_INPUT_NEG           = "INPUT_NEGATIVE"
        PORT_OUTPUT_POS          = "OUTPUT_POSITIVE"
        PORT_OUTPUT_NEG          = "OUTPUT_NEGATIVE"
        PORT_COMMON_MODE         = "COMMON_MODE"
        PORT_CURRENT_SOURCE      = "CURRENT_SOURCE"

        # =========================================================================
        # 2. 内部状态管理 (Internal State)
        # =========================================================================
        
        # 存储所有默认的中文映射 (Immutable for reference)
        _DEFAULT_CHINESE_MAP = {
            STR_DIFF_PAIR:       "差分输入对",
            STR_CASCODE:         "级联结构",
            STR_STD_MIRROR:      "普通电流镜",
            STR_LV_MIRROR:       "低压电流镜",
            STR_LV_MIRROR_PAIR:  "低压镜像对",
            STR_LOAD_TYPICAL:    "典型负载",
            STR_LOAD_A:          "A型负载",
            STR_LOAD_B:          "B型负载",
            STR_LOAD_C:          "C型负载",
            STR_OUTPORT_PAIR:    "输出端对",
            STR_OUTPUT_PAIR:     "逻辑输出对",
            STR_CM_DETECT_A:     "2管共模检测",
            STR_CM_DETECT_B:     "4管共模检测",
            STR_FREQ_COMPENSATE: "频率补偿",
            STR_RC_CM_DETECT:    "RC共模检测",
            STR_SYM_CAPACITOR:   "对称电容",
            STR_TAIL_INPUT:      "输入尾电流源",
            STR_TAIL_COMMON:     "公共尾电流源",
            STR_TAIL_OUTPUT:     "输出尾电流源",
            
            # Tags 的描述 (这里后续要补全)
            TAG_DIODE_MOS:       "二极管连接MOS",
            TAG_IN_CURRENT_BEAM: "处在电流束",
            TAG_ROOT_REF:        "根参考管"
        }

        # 当前生效的映射 (Mutable)
        _CHINESE_NAME_MAP = _DEFAULT_CHINESE_MAP.copy()
        
        # 记录运行时添加的 Keys (用于 reset)
        _DYNAMIC_KEYS = set()

        # =========================================================================
        # 3. 管理方法 (Management Methods) - 补全原有 DeviceTags 的功能
        # =========================================================================

        @classmethod
        def get_chinese_name(cls, key: str) -> str:
            """
            获取常量的中文描述。
            对应旧版: DeviceTags.get_tag(name)
            """
            return cls._CHINESE_NAME_MAP.get(key, key)

        @classmethod
        def list_keys(cls, prefix: str = "") -> dict[str, str]:
            """
            列出指定类别的所有常量及其描述。
            对应旧版: DeviceTags.list_tags()
            
            Args:
                prefix: 筛选前缀，如 "TAG_", "STR_", "REL_", "PORT_"。留空则列出所有。
            """
            result = {}
            # 遍历类属性，过滤掉私有属性和方法
            for name, value in cls.__dict__.items():
                if name.startswith("_") or not isinstance(value, str):
                    continue
                
                if prefix and not name.startswith(prefix):
                    continue
                    
                # 获取对应的中文描述，如果没有则显示 Key 本身
                description = cls._CHINESE_NAME_MAP.get(name, name)
                result[name] = f"{value} ({description})"
            return result

        @classmethod
        def add_key(cls, attr_name: str, value: str, description: str = ""):
            """
            [动态扩展] 在运行时注册新的常量。
            对应旧版: DeviceTags.add_tag()
            
            Args:
                attr_name: 类属性名 (e.g., "TAG_CUSTOM_BLOCK")
                value: 实际字符串值 (e.g., "CUSTOM_BLOCK")
                description: 中文描述 (e.g., "自定义模块")
            """
            if hasattr(cls, attr_name):
                print(f"[AnalysisConfig] 警告: 覆盖已有常量 {attr_name}")
            else:
                cls._DYNAMIC_KEYS.add(attr_name)
                
            setattr(cls, attr_name, value)
            if description:
                cls._CHINESE_NAME_MAP[attr_name] = description
                
            print(f"[AnalysisConfig] 已注册: {attr_name} = '{value}' ({description})")

        @classmethod
        def remove_key(cls, attr_name: str):
            """
            [动态扩展] 删除常量。
            对应旧版: DeviceTags.remove_tag()
            """
            if not hasattr(cls, attr_name):
                print(f"[AnalysisConfig] 错误: 常量 {attr_name} 不存在")
                return
            
            # 从描述映射中移除
            if attr_name in cls._CHINESE_NAME_MAP:
                # 注意：默认映射中的值我们通常保留，或者仅移除动态添加的
                if attr_name not in cls._DEFAULT_CHINESE_MAP: 
                    del cls._CHINESE_NAME_MAP[attr_name]
                    
            # 从类属性中移除
            delattr(cls, attr_name)
            if attr_name in cls._DYNAMIC_KEYS:
                cls._DYNAMIC_KEYS.remove(attr_name)
                
            print(f"[AnalysisConfig] 已移除: {attr_name}")

        @classmethod
        def reset_to_defaults(cls):
            """
            重置所有常量定义到初始状态。
            对应旧版: DeviceTags.reset_to_defaults()
            """
            # 1. 删除所有动态添加的属性
            for attr_name in list(cls._DYNAMIC_KEYS):
                if hasattr(cls, attr_name):
                    delattr(cls, attr_name)
            cls._DYNAMIC_KEYS.clear()
            
            # 2. 重置描述映射
            cls._CHINESE_NAME_MAP = cls._DEFAULT_CHINESE_MAP.copy()
            
            print("[AnalysisConfig] 已重置为默认状态")

        @classmethod
        def get_all_structure_keys(cls) -> set[str]:
            """辅助方法：获取所有已定义的结构 Key (以 STR_ 开头)"""
            return {v for k, v in cls.__dict__.items() if k.startswith("STR_") and isinstance(v, str)}
        
        @classmethod
        def get_all_relation_keys(cls) -> set[str]:
            """辅助方法：获取所有已定义的结构 Key (以 STR_ 开头)"""
            return {v for k, v in cls.__dict__.items() if k.startswith("REL_") and isinstance(v, str)}

        @classmethod
        def get_all_tag_keys(cls) -> set[str]:
            """辅助方法：获取所有已定义的标签 Key (以 TAG_ 开头)"""
            return {v for k, v in cls.__dict__.items() if k.startswith("TAG_") and isinstance(v, str)}

    # 快捷引用配置中心，方便类内部使用 self.AC.STR_XXX
    AC = AnalysisConfig

    class CircuitPorts:
        """
        电路端口常量管理器
        提供对电源、输入、输出、共模信号等网络名称集合的查询与动态修改能力
        """
        
        # ==================== 默认端口定义 ====================
        # 电源正端
        POWER_POSITIVE = {"VDD", "AVDD", "VDDA", "VDD_CORE", "VCC"}
        # 电源负端/地
        POWER_NEGATIVE = {"VSS", "AVSS", "VSSA", "GND", "VEE", "GNDA", "gnd!"}
        # 差分输入正端
        INPUT_POSITIVE = {"VINP", "VIN2", "VIN_POS", "INP", "VIN+"}
        # 差分输入负端
        INPUT_NEGATIVE = {"VINN", "VIN1", "VIN_NEG", "INN", "VIN-"}
        # 输出正端
        OUTPORT_POSITIVE = {"VOUTP", "VOUT2", "VOUT_POS", "OUTP", "VOUT+"}
        # 输出负端
        OUTPORT_NEGATIVE = {"VOUTN", "VOUT1", "VOUT_NEG", "OUTN", "VOUT-"}
        # 共模信号
        COMMON_SIGN = {"VCM", "VCOM"}
        # 电流源参考
        CURRENT_SOURCE = {"IREF", "IIN"}

        # ==================== 查询方法 ====================
        
        @classmethod
        def list_ports(cls) -> Dict[str, Set[str]]:
            """
            查看所有已定义的端口常量
            返回: {端口名称: 名称集合} 的字典
            示例:
                >>> ports = CircuitPort.list_ports()
                >>> print(ports["POWER_POSITIVE"])  # 输出: {'VDD', 'AVDD', ...}
            """
            return {
                k: v.copy() 
                for k, v in cls.__dict__.items() 
                if not k.startswith('_') and isinstance(v, set)
            }

        @classmethod
        def get_port(cls, name: str) -> Optional[Set[str]]:
            """
            获取指定端口名称对应的集合
            参数:
                name: 端口常量名称（如 "POWER_POSITIVE"）
            返回:
                该端口的名称集合，若不存在则返回 None
            示例:
                >>> pos = CircuitPort.get_port("POWER_POSITIVE")
                >>> print(pos)  # 输出: {'VDD', 'AVDD', ...}
            """
            return getattr(cls, name, None)

        # ==================== 修改方法 ====================

        @classmethod
        def add_port(cls, name: str, value_set: Set[str]) -> None:
            """
            添加新的端口常量
            参数:
                name: 新端口名称（必须全大写，可含下划线）
                value_set: 名称字符串集合
            异常:
                ValueError: 名称格式不规范
                TypeError: value_set 不是集合类型
            示例:
                >>> CircuitPort.add_port("POWER_PLL", {"VDD_PLL", "AVDD_PLL"})
            """
            # 验证名称格式
            if not name.isupper() or not name.replace("_", "").isalnum():
                raise ValueError("端口名称必须为大写字母+下划线格式（如 POWER_CUSTOM）")
            
            # 验证类型
            if not isinstance(value_set, set):
                raise TypeError("端口值必须是 set 类型")
            
            # 确保集合元素为字符串
            if not all(isinstance(item, str) for item in value_set):
                raise TypeError("集合中的所有元素必须是字符串")
            
            # 创建副本避免外部修改影响类属性
            setattr(cls, name, value_set.copy())
            print(f"[CircuitPort] 已添加端口常量: {name} = {value_set}")

        @classmethod
        def remove_port(cls, name: str) -> None:
            """
            删除指定的端口常量
            参数:
                name: 要删除的端口名称
            异常:
                AttributeError: 端口不存在
            示例:
                >>> CircuitPort.remove_port("POWER_PLL")
            """
            if hasattr(cls, name):
                delattr(cls, name)
                print(f"[CircuitPort] 已删除端口常量: {name}")
            else:
                raise AttributeError(f"端口常量 '{name}' 不存在")

        # ==================== 元素级操作方法 ====================

        @classmethod
        def add_to_port(cls, name: str, element: str) -> None:
            """
            向现有端口集合中添加单个元素
            参数:
                name: 端口名称
                element: 要添加的网络名称
            异常:
                AttributeError: 端口不存在
                TypeError: 端口值不是集合类型
            示例:
                >>> CircuitPort.add_to_port("POWER_POSITIVE", "VDD_GPU")
            """
            current = getattr(cls, name, None)
            if current is None:
                raise AttributeError(f"端口常量 '{name}' 不存在")
            
            if not isinstance(current, set):
                raise TypeError(f"{name} 不是集合类型，无法添加元素")
            
            current.add(element)
            print(f"[CircuitPort] 已添加 '{element}' 到 {name}")

        @classmethod
        def remove_from_port(cls, name: str, element: str) -> None:
            """
            从端口集合中删除指定元素
            参数:
                name: 端口名称
                element: 要删除的网络名称
            异常:
                AttributeError: 端口不存在
                TypeError: 端口值不是集合类型
            示例:
                >>> CircuitPort.remove_from_port("POWER_POSITIVE", "VDD_OLD")
            """
            current = getattr(cls, name, None)
            if current is None:
                raise AttributeError(f"端口常量 '{name}' 不存在")
            
            if not isinstance(current, set):
                raise TypeError(f"{name} 不是集合类型，无法删除元素")
            
            if element in current:
                current.discard(element)
                print(f"[CircuitPort] 已从 {name} 删除 '{element}'")
            else:
                print(f"[CircuitPort] 警告: '{element}' 不存在于 {name} 中")

        @classmethod
        def reset_to_defaults(cls) -> None:
            """
            重置所有端口常量为默认值
            示例:
                >>> CircuitPort.reset_to_defaults()
            """
            # 仅重置预定义的端口
            cls.POWER_POSITIVE = {"VDD", "AVDD", "VDDA", "VDD_CORE", "VCC"}
            cls.POWER_NEGATIVE = {"VSS", "AVSS", "VSSA", "GND", "VEE", "GNDA", "gnd!"}
            cls.INPUT_POSITIVE = {"VINP", "VIN2", "VIN_POS", "INP", "VIN+"}
            cls.INPUT_NEGATIVE = {"VINN", "VIN1", "VIN_NEG", "INN", "VIN-"}
            cls.OUTPORT_POSITIVE = {"VOUTP", "VOUT2", "VOUT_POS", "OUTP", "VOUT+"}
            cls.OUTPORT_NEGATIVE = {"VOUTN", "VOUT1", "VOUT_NEG", "OUTN", "VOUT-"}
            cls.COMMON_SIGN = {"VCM", "VCOM"}
            cls.CURRENT_SOURCE = {"IREF", "IIN"}
            print("[CircuitPort] 已重置所有端口为默认值")

    class APPConfig:
        """
        别名-端口-参数配置中心（Alias-Port-Parameter Configuration）
        
        设计原则：
        1. 稳定性：ALIAS_CONFIG 与 PORT_CONFIG 定义物理实体，禁止修改已有条目，允许新增条目，警告删除条目。
        2. 灵活性：PARAM_CONFIG 服务于算法逻辑，允许增删改。
        3. 关联性：任何增删操作都会触发关联检查提示，确保逻辑闭环。

        此类定义了从网表解析到分析全过程的数据格式契约，包含三个不可变键的字典：
        1. ALIAS_CONFIG: 定义各种器件类型在分析器中的别名，验证devices_information[1]）
        2. PORT_CONFIG: 定义各种器件类型在分析器中的端口名称，验证devices_information[2]的键）
        3. PARAM_CONFIG: 定义各种器件类型所具有的参数类型，验证devices_information[3]的键）
        
        键的约束：
        - NMOS与PMOS的PORT_CONFIG必须相等
        - CAPACITOR与RESISTOR的PORT_CONFIG必须相等
        - NMOS与PMOS的PARAM_CONFIG必须相等
        这种关联性后续要进行处理，需要考虑要不要为值添加说明（改成dict[str,dict[str,str]]）
        
        **键（大写标识符）代表逻辑上的各种器件类型，不可增删改，仅可修改其对应值**
        """
        
        # ==================== 1. 核心存储 ====================
        # 键: 大写类型标识符 (Internal ID)
        # 值: 分析器中的别名 (Alias)
        ALIAS_CONFIG = {
            "NMOS": "NMOS",
            "PMOS": "PMOS",
            "CAPACITOR": "Capacitor",
            "RESISTOR": "Resistor"
        }
        
        # 键: 大写类型标识符
        # 值: 合法的端口名称集合
        PORT_CONFIG = {
            "NMOS": {"G", "D", "S", "B"},
            "PMOS": {"G", "D", "S", "B"},
            "CAPACITOR": {"PLUS", "MINUS"},
            "RESISTOR": {"PLUS", "MINUS"}
        }
        
        # 键: 大写类型标识符
        # 值: 合法的参数名称集合
        PARAM_CONFIG = {
            "NMOS": {"m", "fw", "l"},
            "PMOS": {"m", "fw", "l"},
            "CAPACITOR": {"l"},
            "RESISTOR": {"segW", "segL"}
        }

        # ==================== 2. DEVICE & PORT (严格模式) ====================

        @classmethod
        def add_device_type(cls, key: str, default_alias: str) -> None:
            """
            [新增] 新增器件类型标识符
            注意：禁止修改已有条目。
            """
            if key in cls.ALIAS_CONFIG:
                raise ValueError(f"[APPConfig] 禁止修改已有器件类型 '{key}'。物理实体定义不应随意变更。")
            
            cls.ALIAS_CONFIG[key] = default_alias
            print(f"[APPConfig] 新增器件类型: {key} (别名: {default_alias})")
            print(f"  RefCheck -> 请检查是否已设计该器件别名相关处理逻辑？")
            print(f"  RefCheck -> 请检查是否已配置 PORT_CONFIG[{key}] 并设计了相关端口处理逻辑？")
            print(f"  RefCheck -> 请检查是否已配置 PARAM_CONFIG[{key}] 并设计了相关参数处理逻辑？")

        @classmethod
        def add_port_config(cls, key: str, ports: Set[str]) -> None:
            """
            [新增] 新增端口定义
            注意：禁止修改已有条目。
            """
            if key in cls.PORT_CONFIG:
                raise ValueError(f"[APPConfig] 禁止修改已有端口定义 '{key}'。物理端口不应随意变更。")
            
            cls.PORT_CONFIG[key] = ports.copy()
            print(f"[APPConfig] 新增端口定义: {key} -> {ports}")
            print(f"  RefCheck -> 请确认该端口集合是否完整描述了器件物理特性？")
            print(f"  RefCheck -> 请检查是否有相关逻辑处理这些端口（如栅极识别等）？")
            print(f"  RefCheck -> 请检查是否已配置 ALIAS_CONFIG[{key}] 并设计了相关器件处理逻辑？")
            print(f"  RefCheck -> 请检查是否已配置 PARAM_CONFIG[{key}] 并设计了相关参数处理逻辑？")

        @classmethod
        def remove_entry_strictly(cls, key: str) -> None:
            """
            [删除] 删减 DEVICE/PORT 条目
            警告：高风险操作。
            """
            if key not in cls.ALIAS_CONFIG and key not in cls.PORT_CONFIG:
                print(f"[APPConfig] 警告: 尝试删除不存在的键 '{key}'")
                return

            print(f"[APPConfig] 警告: 正在删除核心定义 '{key}'！")
            print(f"  RiskCheck -> 请检查现有分析器逻辑是否与被删除器件类型完全无关？")
            print(f"  RiskCheck -> 请检查另外两字典条目是否也应一并删除？")
            
            if key in cls.ALIAS_CONFIG:
                del cls.ALIAS_CONFIG[key]
                print(f"  - 已删除 ALIAS_CONFIG[{key}]")
            
            if key in cls.PORT_CONFIG:
                del cls.PORT_CONFIG[key]
                print(f"  - 已删除 PORT_CONFIG[{key}]")

        # ==================== 3. PARAM (灵活模式) ====================

        @classmethod
        def update_param_config(cls, key: str, params: Set[str]) -> None:
            """
            [增/删/改] 配置参数集合
            允许覆盖已有配置，因为算法变更会导致参数需求变更。
            """
            is_new = key not in cls.PARAM_CONFIG
            
            if not is_new:
                print(f"[APPConfig] 修改已有参数配置: {key}")
                print(f"  LogicCheck -> 请检查现有参数校准/约束逻辑是否适配修改后的参数列表？")
            else:
                print(f"[APPConfig] 新增参数配置: {key}")
                print(f"  RefCheck -> 请确保 ALIAS_CONFIG[{key}] 和 PORT_CONFIG[{key}] 已存在。")
                print(f"  LogicCheck -> 请确保已实现对应的参数提取与校准逻辑。")

            cls.PARAM_CONFIG[key] = params.copy()
            print(f"  - 当前 {key} 参数集合: {params}")

        # ==================== 4. 查询接口 (保持不变) ====================
        
        @classmethod
        def get_device_alias(cls, key: str) -> str:
            if key not in cls.ALIAS_CONFIG:
                raise KeyError(f"未知类型标识符 '{key}'")
            return cls.ALIAS_CONFIG[key]
        
        @classmethod
        def get_identifier_by_type(cls, device_type: str) -> str:
            for key, type_name in cls.ALIAS_CONFIG.items():
                if device_type == type_name:
                    return key
            raise ValueError(f"未知器件类型字符串 '{device_type}'")

        @classmethod
        def get_legal_ports(cls, key: str) -> Set[str]:
            if key not in cls.PORT_CONFIG:
                raise KeyError(f"未配置端口 '{key}'")
            return cls.PORT_CONFIG[key].copy()
        
        @classmethod
        def get_legal_params(cls, key: str) -> Set[str]:
            if key not in cls.PARAM_CONFIG:
                raise KeyError(f"未配置参数 '{key}'")
            return cls.PARAM_CONFIG[key].copy()
        
        @classmethod
        def reset_to_defaults(cls) -> None:
            """
            重置所有配置为默认值
            
            警告: 此操作会丢失所有自定义配置
            """
            cls.ALIAS_CONFIG = {
                "NMOS": "NMOS",
                "PMOS": "PMOS",
                "CAPACITOR": "Capacitor",
                "RESISTOR": "Resistor"
            }
            cls.PORT_CONFIG = {
                "NMOS": {"G", "D", "S", "B"},
                "PMOS": {"G", "D", "S", "B"},
                "CAPACITOR": {"PLUS", "MINUS"},
                "RESISTOR": {"PLUS", "MINUS"}
            }
            cls.PARAM_CONFIG = {
                "NMOS": {"m", "fw", "l"},
                "PMOS": {"m", "fw", "l"},
                "CAPACITOR": {"l"},
                "RESISTOR": {"segW", "segL"}
            }
            print("[APPConfig] 已重置所有配置为默认值")

        @classmethod
        def list_all_identifiers(cls) -> List[str]:
            """列出所有大写类型标识符"""
            return list(cls.ALIAS_CONFIG.keys())
        
        @classmethod
        def get_config_summary(cls) -> Dict[str, Dict]:
            """
            获取当前APP配置
            
            返回:
                {
                    "NMOS": {
                        "alias": "NMOS",
                        "ports": {"G", "D", "S", "B"},
                        "params": {"m", "fw", "l"}
                    },
                    ...
                }
            """
            return {
                key: {
                    "alias": cls.ALIAS_CONFIG[key],
                    "ports": cls.PORT_CONFIG[key].copy(),
                    "params": cls.PARAM_CONFIG[key].copy()
                }
                for key in cls.ALIAS_CONFIG.keys()
            }

    @dataclass
    class DeviceSub:
        """存储每个Device所属子结构实例索引"""
        sub_type: str
        sub_id: str

    @dataclass
    class Device:
        """存储analyzer识别到的元器件"""
        name: str   #器件名称
        type: str   #器件类型引用
        terminals: Dict[str, str]   #端口字典，键为端口名称，值为连接的网络名称
        params: Dict[str, str]  #参数字典，键为参数名称，值为参数值字符串
        tags: Set[str] = field(default_factory=set) #器件标签
        substructures: List['CircuitAnalyzer.DeviceSub'] = field(default_factory=list)    #器件所属子结构实例引用列表

    # =============================================================================
    # 2. 约束对象协议 (Constraint Protocol)
    # =============================================================================

    class ConstraintType(Enum):
        # 这里RATIO根本没用上
        EQUAL   = auto()    # 强相等 (l=l, fw=fw)
        RATIO_W = auto()    # 宽度比例 (fw_target = fw_source * r_raw)
        # SUM   = auto()    # 预留：求和关系

    @dataclass
    class Constraint:
        """
        [协议] 描述两个器件参数之间的约束关系。
        替代了原有的字符串 "M1_fw = M2_fw"。
        """
        target_dev_name: str
        target_param: str
        source_dev_name: str
        source_param: str
        type: "CircuitAnalyzer.ConstraintType" = CircuitAnalyzer.ConstraintType.EQUAL #type: ignore
        
        def __repr__(self):
            op = "==" if self.type == CircuitAnalyzer.ConstraintType.EQUAL else "~="
            return f"Constraint({self.target_dev_name}.{self.target_param} {op} {self.source_dev_name}.{self.source_param})"

        # --- 辅助构造工厂方法 ---
        @staticmethod
        def eq(target: str, source: str, param: str) -> 'CircuitAnalyzer.Constraint':
            """创建单个参数相等约束"""
            return CircuitAnalyzer.Constraint(target, param, source, param, CircuitAnalyzer.ConstraintType.EQUAL)

        @staticmethod
        def all_eq(target: str, source: str) -> List['CircuitAnalyzer.Constraint']:
            """创建标准MOS管三参数(l, fw, m)相等约束"""
            return [
                CircuitAnalyzer.Constraint.eq(target, source, 'l'),
                CircuitAnalyzer.Constraint.eq(target, source, 'fw'),
                CircuitAnalyzer.Constraint.eq(target, source, 'm')
            ]

    # =============================================================================
    # 3. 逻辑载体 (SubStructure Type)
    # =============================================================================

    class SubStructureType:
        """
        [逻辑载体] 统一管理子结构的定义、识别与约束生成。
        合并了原有的 SubStructureType 与 "StructureDefinition" 概念。
        """
        def __init__(
            self,
            key: str,                                        # AnalysisConfig.STR_XXX
            display_name: str,                               # 中文显示名
            required_tags: Set[str],                         # 必须包含的 Tags
            aggregation_rule: Callable[[Set[str]], bool],    # 聚合校验逻辑
            constraint_generator: Callable[[List[CircuitAnalyzer.Device]], List[CircuitAnalyzer.Constraint]] # 约束生成逻辑
        ):
            self.key = key
            self.display_name = display_name
            self.required_tags = required_tags
            self.aggregation_rule = aggregation_rule
            self.constraint_generator = constraint_generator

        def generate_id(self, members: List[CircuitAnalyzer.Device]) -> str:
            """统一生成 ID: KEY_Name1_Name2"""
            # 假设 members 是 Device 对象，具有 name 属性
            sorted_names = sorted([d.name for d in members])
            return f"{self.key}_{'_'.join(sorted_names)}"

    @dataclass
    class CircuitSub:
        """存储整个Circuit所包含子结构实例"""
        sub_id: str
        type: str
        members: List[str]
        constraints: List[CircuitAnalyzer.Constraint]

    @dataclass
    class Circuit:
        """
            存储 Analyzer 识别到的整个电路。
            初始化时所有容器自动建立为空。
        """
        # 识别到的器件字典
        devices_dict: Dict[str, 'CircuitAnalyzer.Device'] = field(default_factory=dict)

        # 登记的子结构（电路中实际存在的子结构）
        substructures: List['CircuitAnalyzer.CircuitSub'] = field(default_factory=list)
        # 电流路径
        current_paths: List[List[str]] = field(default_factory=list)
        # 电流束
        current_beams: Dict[str, List[List[str]]] = field(default_factory=dict)
        # 电流束路径
        current_beam_paths: Dict[str, List[Set[str]]] = field(default_factory=dict)
        # 电流束网络
        beam_net_sets: Dict[str, Set[str]] = field(default_factory=dict)

    class ConstraintLibrary:
        """
        [规则库] ConstraintLibrary
        
        设计原则：
        1. 严格复刻 temprefine.py 中的原始约束逻辑。
        2. 普通镜像管不生成 fw/m 约束（交由后续 r_raw 校准处理）。
        3. 统一使用 AnalysisConfig 中的常量。
        """
        # =========================================================================
        # 1. 基础配对规则 (保持原样)
        # =========================================================================

        @staticmethod
        def rule_pair_strict(members: List['CircuitAnalyzer.Device']) -> List['CircuitAnalyzer.Constraint']:
            """
            [严格配对] 对应: 差分对, 输出对, 共模检测A, C型负载, 典型负载(pair部分)
            原始逻辑: 成员间 fw/l/m 完全相等。
            """
            if len(members) < 2:
                return []
            
            ref = members[0]
            
            constraints = []
            for target in members[1:]:
                constraints.extend(CircuitAnalyzer.Constraint.all_eq(target.name, ref.name))
                
            return constraints

        # =========================================================================
        # 2. 级联结构规则 (保持原样)
        # =========================================================================

        @staticmethod
        def rule_cascode(members: List['CircuitAnalyzer.Device']) -> List['CircuitAnalyzer.Constraint']:
            """
            [级联]
            原始逻辑: 找到 Main，所有 Slave 的 l/fw/m 必须与 Main 相同。
            """
            AC = CircuitAnalyzer.AnalysisConfig
            constraints = []
            
            try:
                main = next(d for d in members if AC.TAG_CASCODE_MAIN in d.tags)
            except StopIteration:
                return [] 
                
            for dev in members:
                if dev.name == main.name:
                    continue
                constraints.extend(CircuitAnalyzer.Constraint.all_eq(dev.name, main.name))
                
            return constraints

        # =========================================================================
        # 3. 电流镜规则 (严格复刻原始逻辑)
        # =========================================================================

        @staticmethod
        def rule_std_mirror(members: List['CircuitAnalyzer.Device']) -> List['CircuitAnalyzer.Constraint']:
            """
            [普通电流镜]
            原始逻辑复刻:
            - 所有镜像管: l 必须约束 (m.l = ref.l)。
            - 偏置镜像管 (BIAS):
                - 若 Ref 是 ROOT_REF: 偏置管之间 fw/m 互等 (独立于 Ref)。
                - 若 Ref 非 ROOT_REF: 偏置管 fw/m = Ref.fw/m。
            - 普通镜像管: **不生成** fw/m 约束 (原代码未对非偏置管生成 fw/m 约束字符串)。
            """
            AC = CircuitAnalyzer.AnalysisConfig
            constraints = []
            
            try:
                ref = next(d for d in members if AC.TAG_STD_MIRROR_REF in d.tags)
            except StopIteration:
                return [] # "# 错误：普通电流镜缺少参考管"

            is_ref_root = AC.TAG_ROOT_REF in ref.tags
            bias_mirror_names = []  # 用于 Root Ref 时的互锁

            for m in members:
                if m.name == ref.name:
                    continue
                
                # --- 1. l 约束  ---
                # 原代码: base = [f"{m.name}_l = {ref.name}_l"]
                constraints.append(CircuitAnalyzer.Constraint.eq(m.name, ref.name, 'l'))

                is_bias = AC.TAG_STD_MIRROR_BIAS in m.tags

                # --- 2. fw/m 约束 ---
                if is_bias:
                    if is_ref_root:
                        # Case 1: 收集起来稍后互锁
                        bias_mirror_names.append(m.name)
                    else:
                        # Case 2: 非Root Ref，偏置管严格跟随 Ref
                        # 原代码: base.extend([f"{m.name}_m = {ref.name}_m", f"{m.name}_fw = {ref.name}_fw"])
                        constraints.append(CircuitAnalyzer.Constraint.eq(m.name, ref.name, 'm'))
                        constraints.append(CircuitAnalyzer.Constraint.eq(m.name, ref.name, 'fw'))
                
                # 注意：对于普通镜像管 (is_bias=False)，原代码在此处不生成 fw/m 约束。
                # 它们将在 _precompute_r_raw_map 和 _calibrate_device_params 阶段被处理。

            # --- 3. 根参考管的偏置镜像管互锁 ---
            if is_ref_root and len(bias_mirror_names) > 1:
                first_m_name = bias_mirror_names[0]
                for other_m_name in bias_mirror_names[1:]:
                    # 原代码: constraints.extend([f"{other_m}_m = {first_m}_m", f"{other_m}_fw = {first_m}_fw"])
                    constraints.append(CircuitAnalyzer.Constraint(other_m_name, 'm', first_m_name, 'm'))
                    constraints.append(CircuitAnalyzer.Constraint(other_m_name, 'fw', first_m_name, 'fw'))

            return constraints

        @staticmethod
        def rule_lv_mirror(members: List['CircuitAnalyzer.Device']) -> List['CircuitAnalyzer.Constraint']:
            """
            [低压电流镜]
            原始逻辑复刻:
            1. 上层参考管 (Upper Ref) 与 下层参考管 (Lower Ref): fw/l/m 全等。
            2. 镜像管 (无论是 Upper 还是 Lower):
            - l: 始终等于 Lower Ref.l。
            - 若为偏置镜像管 (BIAS): fw/m 等于 Lower Ref.fw/m。
            - 若为普通镜像管: **不生成** fw/m 约束。
            """
            AC = CircuitAnalyzer.AnalysisConfig
            constraints = []
            
            try:
                # 原代码: [d for d in members if self.DeviceTags.LV_MIRROR_UPPER_REF in d.tags][0]
                upper_ref = next(d for d in members if AC.TAG_LV_UPPER_REF in d.tags)
                lower_ref = next(d for d in members if AC.TAG_LV_LOWER_REF in d.tags)
            except StopIteration:
                return [] # "# 错误：低压电流镜成员不完整"

            # 1. 上下参考管全等
            # 原代码: constraints.extend([f"{upper_ref.name}_fw = {lower_ref.name}_fw", ...])
            constraints.extend(CircuitAnalyzer.Constraint.all_eq(upper_ref.name, lower_ref.name))

            # 获取所有镜像管 (包括 Upper Mirror, Lower Mirror, Bias Mirror)
            # 在 Graph 架构中它们都通过 relation 连接，这里直接遍历 members 排除 refs
            refs = {lower_ref.name, upper_ref.name}
            
            for m in members:
                if m.name in refs or AC.TAG_LV_UPPER_BIAS in m.tags:
                    continue
                
                # --- l 约束 (始终应用) ---
                # 原代码对 Upper/Lower Mirror 都执行: base = [f"{m.name}_l = {lower_ref.name}_l"]
                constraints.append(CircuitAnalyzer.Constraint.eq(m.name, lower_ref.name, 'l'))
                
                # --- fw/m 约束 (仅针对偏置管) ---
                is_bias = AC.TAG_LV_BIAS_MIRROR in m.tags
                
                if is_bias:
                    # 原代码: if ...BIAS_MIRROR...: base.extend([m=m, fw=fw])
                    constraints.append(CircuitAnalyzer.Constraint.eq(m.name, lower_ref.name, 'm'))
                    constraints.append(CircuitAnalyzer.Constraint.eq(m.name, lower_ref.name, 'fw'))

            return constraints

        # =========================================================================
        # 4. 负载与多管结构规则 (保持原样)
        # =========================================================================

        @staticmethod
        def rule_load_typical(members: List['CircuitAnalyzer.Device']) -> List['CircuitAnalyzer.Constraint']:
            """
            [典型负载] / [A型/B型负载] / [4管共模检测]
            原始逻辑: 最后一个器件作为参考，其他器件向其看齐 (fw/l/m 全等)。
            """
            if not members:
                return []
                
            ref = members[-1]
            constraints = []
            
            for dev in members[:-1]:
                constraints.extend(CircuitAnalyzer.Constraint.all_eq(dev.name, ref.name))
                
            return constraints

        # =========================================================================
        # 5. 无源器件 (RC) 规则 (保持原样)
        # =========================================================================

        @staticmethod
        def rule_rc_group(members: List['CircuitAnalyzer.Device']) -> List['CircuitAnalyzer.Constraint']:
            """
            [RC组] 适用于: 频率补偿, RC共模检测, 对称电容
            原始逻辑:
            - 电阻: segW, segL 相等 (如果存在)。
            - 电容: l 相等 (如果存在)。
            """
            constraints = []
            resistors = [d for d in members if d.type == "Resistor"]
            capacitors = [d for d in members if d.type == "Capacitor"]
            
            # 约束电阻
            if len(resistors) > 1:
                ref_r = resistors[0]
                for r in resistors[1:]:
                    if "segW" in ref_r.params:
                        constraints.append(CircuitAnalyzer.Constraint.eq(r.name, ref_r.name, "segW"))
                    if "segL" in ref_r.params:
                        constraints.append(CircuitAnalyzer.Constraint.eq(r.name, ref_r.name, "segL"))

            # 约束电容
            if len(capacitors) > 1:
                ref_c = capacitors[0]
                has_l = "l" in ref_c.params
                
                for c in capacitors[1:]:
                    if has_l:
                        constraints.append(CircuitAnalyzer.Constraint.eq(c.name, ref_c.name, "l"))
                        
            return constraints
        
    def _init_substructure_registry(self):
        """
        [核心] 初始化子结构类型注册表。
        将 Config Key (是什么) 映射到 Logic (怎么识别) 和 Rules (怎么约束)。
        """
        AC = self.AC
        CL = self.ConstraintLibrary
        
        # 辅助函数：简化注册代码
        def reg(key, display, tags, rule_func):
            self.substructure_types[key] = self.SubStructureType(
                key=key,
                display_name=display,
                required_tags=tags,
                aggregation_rule=lambda roles: tags.issubset(roles),
                constraint_generator=rule_func
            )

        # --- A. 基础结构 ---
        # 差分输入对
        reg(AC.STR_DIFF_PAIR, "差分输入对", {AC.TAG_DIFF_POS, AC.TAG_DIFF_NEG}, CL.rule_pair_strict)
        # 级联
        reg(AC.STR_CASCODE, "级联结构", {AC.TAG_CASCODE_MAIN, AC.TAG_CASCODE_SLAVE}, CL.rule_cascode)

        # --- B. 电流镜 ---
        reg(AC.STR_STD_MIRROR, "普通电流镜", {AC.TAG_STD_MIRROR_REF, AC.TAG_STD_MIRROR_MIRROR}, CL.rule_std_mirror)
        
        # 低压电流镜需要检查4个标签
        reg(AC.STR_LV_MIRROR, "低压电流镜", 
            {AC.TAG_LV_LOWER_REF, AC.TAG_LV_UPPER_REF, AC.TAG_LV_UPPER_MIRROR, AC.TAG_LV_LOWER_MIRROR}, # 不考虑上层偏置管
            CL.rule_lv_mirror)
            
        reg(AC.STR_LV_MIRROR_PAIR, "低压镜像对", {AC.TAG_LV_PAIR}, CL.rule_pair_strict)

        # --- C. 负载与输出 ---
        # 负载类通常复用 pair_strict 或 load_typical
        reg(AC.STR_LOAD_TYPICAL, "典型负载", {AC.TAG_LOAD_TYP}, CL.rule_load_typical)
        reg(AC.STR_LOAD_A, "A型负载", {AC.TAG_LOAD_A_DIO}, CL.rule_pair_strict)
        reg(AC.STR_LOAD_B, "B型负载", {AC.TAG_LOAD_B}, CL.rule_pair_strict)
        reg(AC.STR_LOAD_C, "C型负载", {AC.TAG_LOAD_C}, CL.rule_pair_strict) # 原逻辑用 pair_constraint

        # 输出端对 / 输出对
        reg(AC.STR_OUTPORT_PAIR, "输出端对", {AC.TAG_OUTPORT_POS, AC.TAG_OUTPORT_NEG}, CL.rule_pair_strict)
        reg(AC.STR_OUTPUT_PAIR, "逻辑输出对", {AC.TAG_OUTPUT_POS, AC.TAG_OUTPUT_NEG}, CL.rule_pair_strict)

        # --- D. 共模与 RC ---
        # 共模检测
        reg(AC.STR_CM_DETECT_A, "2管共模检测", {AC.TAG_CM_2MOS}, CL.rule_pair_strict)
        reg(AC.STR_CM_DETECT_B, "4管共模检测", {AC.TAG_CM_4MOS}, CL.rule_load_typical) # 复用 typical load 逻辑

        # RC 结构
        reg(AC.STR_FREQ_COMPENSATE, "频率补偿", {AC.TAG_COMPENSATE}, CL.rule_rc_group)
        reg(AC.STR_RC_CM_DETECT, "RC共模检测", {AC.TAG_RC_CM_DETECT}, CL.rule_rc_group)
        reg(AC.STR_SYM_CAPACITOR, "对称电容", {AC.TAG_SYM_CAPACITOR}, CL.rule_rc_group) # 复用 rc group 逻辑

    # ------------------------------
    # 3.初始化
    # ------------------------------
    def __init__(self):
        """
        CircuitAnalyzer 初始化
        遵循原则：
        1. 必须使用 Graph-Driven Storage (tag_index, relation_graph, device_groups)。
        2. 禁止初始化特定业务逻辑的缓存列表 (如 diff_pair_positive, cascode_cache 等)。
        3. 所有子结构类型注册必须通过 registry 完成。
        """
        # 1. 基础拓扑容器
        self.circuit = self.Circuit()   
        self.net_device_map: DefaultDict[str, List[str]] = defaultdict(list)
        self.config_complete: bool = False

        # 2. [核心] 图驱动存储 (Graph-Driven Storage)
        # 替代原有的 self.diff_pair_positive, self.outport_pair 等分散列表
        # 结构: { TAG_KEY: {dev_name, ...} }
        self.tag_index: DefaultDict[str, Set[str]] = defaultdict(set)
        
        # 替代原有的 cascode_cache, lv_current 等分散字典
        # 结构: { source_name: { REL_KEY: [target_name, ...] } }
        self.relation_graph: DefaultDict[str, DefaultDict[str, List[str]]] = defaultdict(lambda: defaultdict(list))
        
        # 替代原有的 outport_pair, typ_load 等 List[List]
        # 结构: { GROUP_KEY: [[name1, name2], ...] }
        self.device_groups: DefaultDict[str, List[List[str]]] = defaultdict(list)

        # 3. 逻辑注册表
        self.substructure_types: Dict[str, 'CircuitAnalyzer.SubStructureType'] = {}
        self._init_substructure_registry()
        
        # 存储最终生成的参数等效组 (List of param strings)
        self.constraint_groups: List[List[str]] = []
        
        # 4. 分析结果存储
        # 存储 r_raw 真值计算结果: { copy_name: (ref_name, r_raw_value) }
        self.copy_tube_r_raw_map: Dict[str, Tuple[str, float]] = {} 

        # 参数存储 (保留用于参数校准)
        self.calibrate_params: Dict[str,Dict[str,str]] = {}
        self.device_params: Dict[str, Dict[str, str]] = {}
        
        # 辅助缓存 (仅保留极少数必要的中间态)
        self.top_nodes: List['CircuitAnalyzer.Device'] = []
        self._flat_beam_cache: Optional[List[Set[str]]] = None

    @classmethod
    def from_parsed_data(cls, devices_information: List[List[Any]], config_complete: bool):
        """
        校验网表解析数据，实例化Device，创建分析器

        验证契约（由APPConfig强制执行）：
        - devices_information[i][1] 必须等于 APPConfig.ALIAS_CONFIG[identifier]
        - devices_information[i][2] 的键必须是 APPConfig.PORT_CONFIG[identifier] 的子集
        - devices_information[i][3] 的键必须是 APPConfig.PARAM_CONFIG[identifier] 的子集
        """
        analyzer = cls()
        analyzer.config_complete = config_complete
        
        if not isinstance(devices_information, list):
            raise TypeError("devices_information必须是列表")

        # APPConfig验证
        for idx, dev_info in enumerate(devices_information):
            if len(dev_info) != 4:
                raise ValueError(f"器件信息格式错误（索引{idx}）: 期望4元素，实际{len(dev_info)}")

            # 验证器件类型引用格式
            dev_type_str = dev_info[1]
            identifier = cls.APPConfig.get_identifier_by_type(dev_type_str)
            
            # 验证端口配置与格式
            terminals = dev_info[2]
            legal_ports = cls.APPConfig.get_legal_ports(identifier)
            if not set(terminals.keys()).issubset(legal_ports):
                raise ValueError(f"器件 '{dev_info[0]}' 端口非法")
            
            # 验证参数类型与格式
            params = dev_info[3]
            legal_params = cls.APPConfig.get_legal_params(identifier)
            if not set(params.keys()).issubset(legal_params):
                raise ValueError(f"器件 '{dev_info[0]}' 参数非法")
        
            # 验证通过，Device实例化
            name = dev_info[0]
            analyzer.device_params[name] = params

            # 2. 创建Device实例并存入字典
            device_obj = cls.Device(
                name=name,
                type=dev_type_str,
                terminals=terminals,
                params=params
            )
            analyzer.circuit.devices_dict[name] = device_obj

            # 构建网络-器件映射
            nets = set(net for net in terminals.values())  # 避免重复添加
            for net in nets:
                analyzer.net_device_map[net.lower()].append(name)

        analyzer._run_analysis_pipeline()
        return analyzer
    
    @classmethod
    def from_spice_netlist(
        cls,
        netlist_path: str,
        parser_class: Optional[type] = None
    ) -> 'CircuitAnalyzer':
        """
        从SPICE网表创建分析器 - 最常用入口
        
        Args:
            netlist_path: SPICE网表文件路径
            devparam_types: 器件参数类型设置（None使用默认）
            parser_class: 自定义解析器类（None使用默认SPICEParser）
            这里要根据默认网表解析器进行调整
        
        Returns:
            CircuitAnalyzer实例
        """
        # 选择解析器
        if parser_class is None:
            parser_class = cls.DefaultSpiceParser
        
        # 解析网表
        parser = parser_class(netlist_path)
        devices_info = parser.parse()
        
        # 自动检测配置完整性
        config_complete = parser.check_config_complete()
        
        # 使用统一入口创建
        return cls.from_parsed_data(
            devices_info,
            config_complete=config_complete
        )
    
    # ==================== 默认网表解析器 ====================

    class DefaultSpiceParser:
        """
        默认SPICE网表解析器
        这里之后要根据实际SPICE网表格式进行扩展和修改
        支持的格式：
        - M1 D G S B model w=1u l=500n m=2
        - R1 PLUS MINUS model r=1k
        - C1 PLUS MINUS model c=1p
        
        可通过继承扩展支持其他格式
        """
        
        # 可覆盖的类变量
        DEVICE_TYPE_MAP = {
            "M": "NMOS",
            "MP": "PMOS",
            "R": "Resistor",
            "C": "Capacitor"
        }
        
        PARAM_NAME_MAP = {
            "w": "fw",      # 宽度
            "l": "l",       # 长度
            "m": "m",       # 倍数
            "r": "segW",    # 电阻宽度（简化映射）
            "c": "l"        # 电容长度（简化映射）
        }
        
        def __init__(self, netlist_path: str):
            self.netlist_path = netlist_path
            self.devices_info = []
        
        def parse(self) -> List[List[Any]]:
            """解析网表文件"""
            self.devices_info = []
            
            with open(self.netlist_path, 'r', encoding='utf-8') as f:
                for line_num, line in enumerate(f, 1):
                    line = line.strip()
                    if not line or line.startswith('*'):
                        continue
                    
                    try:
                        dev_info = self._parse_line(line)
                        if dev_info:
                            self.devices_info.append(dev_info)
                    except Exception as e:
                        raise ValueError(f"解析失败行{line_num}: {line}\n错误: {e}")
            
            return self.devices_info
        
        def _parse_line(self, line: str) -> Optional[List[Any]]:
            """解析单行器件定义"""
            parts = line.split()
            if not parts:
                return None
            
            # 提取器件名称和类型
            name = parts[0]
            type_symbol = ''.join(filter(str.isalpha, name[:2]))
            dev_type = self.DEVICE_TYPE_MAP.get(type_symbol)
            
            if not dev_type:
                print(f"警告: 跳过未知器件 '{name}'")
                return None
            
            # 提取端口（根据类型）
            terminals = {}
            if dev_type in ["NMOS", "PMOS"]:
                terminals = {
                    "D": parts[1],
                    "G": parts[2],
                    "S": parts[3],
                    "B": parts[4]
                }
                param_start = 5
            else:
                terminals = {
                    "PLUS": parts[1],
                    "MINUS": parts[2]
                }
                param_start = 3
            
            # 提取参数
            params = {}
            for part in parts[param_start:]:
                if '=' in part:
                    k, v = part.split('=')
                    mapped_name = self.PARAM_NAME_MAP.get(k, k)
                    params[mapped_name] = v
            
            return [name, dev_type, terminals, params]
        
        def check_config_complete(self) -> bool:
                """
                检查所有器件是否配置了所有必需参数
                
                Returns:
                    True: 所有必需参数值非空
                """
                if not self.devices_info:
                    return False
                
                for name, dev_type, _, params in self.devices_info:
                    required_params = CircuitAnalyzer.DEFAULT_PARAM_TYPES.get(dev_type, set())
                    
                    # 检查每个必需参数
                    for req_param in required_params:
                        if params.get(req_param, "") == "":
                            print(f"参数不完整: 器件 '{name}' 的 '{req_param}' 为空")
                            return False
                
                return True
    
    def _run_analysis_pipeline(self):
        """
        执行分析流程
        
        根据config_complete标志决定是否执行参数校准
        这里的流程要确保正确
        """
        # ----------------------------------------特殊器件检测---------------------------------------------
        self._mark_obvious_tags()  # 标记二极管器件、输入器件、顶层节点、共模检测器件
        self._mark_outport_devices()  # 标记输出端管与频率补偿RC和共模检测RC
        self._mark_common_mode_detect_b()  # 标记4管共模检测器件

        self._analyze_diode_mos_structures()  # 标记级联器件与普通电流镜器件
        self._mark_root_reference_path()  # 标记普通电流镜根参考管
        self._detect_low_voltage_current_mirrors()  # 标记低压电流镜，与普通电流镜解耦合

        # 1. 生成电流路径，包含网络
        self.generate_current_paths()
        # 2. 生成电流束，生成电流束路径，生成电流束网络，标记电流束器件
        self.analyze_current_beams()
        # 3.标记两种电流镜中的偏置管
        self._mark_bias_mirrors()

        # ---------------------------------------子结构检测与登记--------------------------------------------
        # 0.登记大部分子结构
        self._register_beam_substructures()

        # 1.登记同一电流路径中的低压电流镜镜像对
        self._register_lv_mirror_pairs()

        # 2. 登记低压电流镜
        self._register_lv_mirrors()

        # 3. 登记普通电流镜
        self._register_current_mirrors()

        # 缓存输入、输出尾电流源
        self._get_tail_current()
        # 缓存输出对
        self._get_output_pair()

        # 4. 登记 RC 子结构
        self._register_rc_structures()

        # 5. 登记对称电容
        self._register_sym_capacitors()

        #----------------------------------------生成参数约束---------------------------------------------------
        self._generate_constraint_groups()
        # ---------------------------------------条件执行参数校准-----------------------------------------------
        if self.config_complete:
            print("[阶段5] 生成约束并校准参数...")
            self._precompute_r_raw_map()
            self._calibrate_device_params()
        else:
            print("[警告] 参数配置不完整，跳过参数校准")
            self.calibrate_params = copy.deepcopy(self.device_params)

    # -------------------------------------------------------------------------------------------------------------------------------------------
    # --------------------------------------------------------核心工具方法------------------------------------------------------------------------
    # -------------------------------------------------------------------------------------------------------------------------------------------

    # ---------------连接到特定导线检测---------------------
    def _net_matches(self, net_name: str, target_set: Set[str]) -> bool:
        """网络匹配：大小写不敏感"""
        if not net_name:
            return False
        target_lower = {s.lower() for s in target_set}
        return net_name.lower() in target_lower

    # ------------对称电容识别辅助函数-----------
    def _is_net_powerorgnd(self, net: str) -> bool:
        """检查网络是否连接到正电源或负电源"""
        return self._net_matches(net,self.CircuitPorts.POWER_POSITIVE) or self._net_matches(net,self.CircuitPorts.POWER_NEGATIVE)

    def _is_net_power(self, net_name: str) -> bool:
        """检查是否为正电源"""
        return self._net_matches(net_name, self.CircuitPorts.POWER_POSITIVE)
    
    def _is_net_ground(self, net_name: str) -> bool:
        """检查是否为地/负电源"""
        return self._net_matches(net_name, self.CircuitPorts.POWER_NEGATIVE)
    # ------------对称电容识别辅助函数-----------
    def _get_mos_on_net(self, net: str, exclude_devices: Set[str]) -> Set[str]:
        """获取指定网络上连接的MOS管，排除指定器件"""
        if not net:
            return set()

        mos_set = set()
        dev_names = self.net_device_map.get(net.lower(), [])
        for name in dev_names:
            if name in exclude_devices:
                continue
            dev = self.circuit.devices_dict.get(name)
            if dev and dev.type in ["PMOS", "NMOS"]:
                mos_set.add(name)
        return mos_set

    # --------对称电容识别核心函数 ---------
    def _check_mos_sets_in_one_beam(self, set_mos_1: Set[str], set_mos_2: Set[str]) -> bool:
        """
        检查两个MOS管集合是否同时被包含在 *至少一个* 电流束中。
        """
        set_total_mos = set_mos_1.union(set_mos_2)
        if not set_total_mos:
            return False  # 两个集合都未连接到任何MOS管
        # 缓存压平的电流束
        if self._flat_beam_cache is None:
            self._flat_beam_cache = [
                set().union(*beam_path)
                for beam_path in self.circuit.current_beam_paths.values()
            ]

        for devices_in_this_beam in self._flat_beam_cache:
            if set_total_mos.issubset(devices_in_this_beam):
                return True  # 匹配成功
        return False

    # ------------------连接到电源正端检测--------------------
    def _is_top_node(self, device: 'CircuitAnalyzer.Device') -> bool:
        """
        判断器件是否为顶层节点(连接电源正端，少了这个器件电路无法工作)
        电容不被视作构成电流路径（少了这个电容电路仍可以工作，只是指标恶化）
        """
        if device.type == "PMOS":
            # PMOS 源极接电源
            return self._is_net_power(device.terminals.get("S", ""))
        elif device.type == "NMOS":
            # NMOS 漏极接电源
            return self._is_net_power(device.terminals.get("D", ""))
        elif device.type == "Resistor":
            # 电阻任一端接电源
            nets = list(device.terminals.values())
            return any(self._is_net_power(net) for net in nets)
        return False
    
    # =========================================================================
    # 2. 统一操作接口 (Unified Operations)
    # =========================================================================

    def add_tag(self, device: Union[str, 'Device'], tag: str):
        """
        [统一接口] 给器件打标签并同步索引。
        tag: 必须是 AnalysisConfig.TAG_XXX
        """
        if isinstance(device, str):
            device_obj = self.circuit.devices_dict.get(device)
            if not device_obj:
                print(f"[Warning] 尝试给不存在的器件 {device} 打标签 {tag}")
                return
        else:
            device_obj = device

        if tag not in device_obj.tags:
            device_obj.tags.add(tag)
            self.tag_index[tag].add(device_obj.name)

    def remove_tag(self, device: Union[str, 'Device'], tag: str):
        """[统一接口] 移除标签"""
        if isinstance(device, str):
            device_obj = self.circuit.devices_dict.get(device)
        else:
            device_obj = device
        
        if device_obj and tag in device_obj.tags:
            device_obj.tags.remove(tag)
            self.tag_index[tag].discard(device_obj.name)
        else: 
            print(f"删除器件标签{tag}失败")

    def add_group(self, group_key: str, members: List[str]):
        """
        [统一接口] 记录一组器件。
        group_key: 必须是 AnalysisConfig.STR_XXX
        """
        self.device_groups[group_key].append(members)

    def add_relation(self, source: str, relation_key: str, target: str):
        """
        [统一接口] 记录器件关系。
        relation_key: 必须是 AnalysisConfig.REL_XXX
        """
        self.relation_graph[source][relation_key].append(target)

    def get_relations(self, source: str, relation_key: str) -> List[str]:
        """
        [统一接口] 获取关系目标列表。
        安全读取：如果 source 或 relation_key 不存在，返回空列表，而不是报错。
        """
        # 即使 self.relation_graph 是 defaultdict，
        # 使用 .get() 可以避免在仅读取时意外创建空的 source 条目。
        source_relations = self.relation_graph.get(source)
        if source_relations is None:
            return []
        
        return source_relations.get(relation_key, [])
    
    def get_names_by_tag(self, tag: str) -> Set[str]:
        """[统一接口] 获取拥有标签的器件名"""
        return self.tag_index.get(tag, set()).copy()
    
    def get_devices_by_tag(self, tag: str) -> List['Device']:
        """[统一接口] 获取拥有标签的器件对象"""
        names = self.tag_index.get(tag, set())
        return [self.circuit.devices_dict[n] for n in names if n in self.circuit.devices_dict]

    # -------------------------------------------------------特殊器件检测------------------------------------------------------------
    def _mark_obvious_tags(self):
        """
        [重构版] 基础标签识别
        
        逻辑保持不变：
        1. G/D短接 -> 二极管连接 (TAG_DIODE_MOS)
        2. 连接电源正端 -> 顶层节点 (self.top_nodes)
        3. 栅极接输入端口 -> 差分输入管 (TAG_DIFF_POS/NEG)
        4. 栅极接共模端口 -> 外侧共模管 (TAG_CM_OUTER)
        
        **独立，不依赖其他函数**
        """
        AC = self.AC  # 快捷引用
        
        for device in self.circuit.devices_dict.values():
            # --------------------- 1. 检测二极管连接MOS管 ------------------
            if device.type in ["PMOS", "NMOS"]:
                g_net = device.terminals.get("G")
                d_net = device.terminals.get("D")
                # 检查 G 和 D 是否连接到同一网络
                if g_net and d_net and self._net_matches(g_net, {d_net}):
                    self.add_tag(device, AC.TAG_DIODE_MOS)

            # ----------------------- 2. 识别顶层节点 -------------------------
            # 顶层节点用于生成电流路径，存储在辅助缓存 top_nodes 中
            if self._is_top_node(device):
                self.top_nodes.append(device)

            # ------------------------ 3. 标记差分输入管 --------------------------
            if device.type in ["PMOS", "NMOS"]:
                g_net = device.terminals.get("G")
                if g_net:
                    if self._net_matches(g_net, self.CircuitPorts.INPUT_POSITIVE):
                        self.add_tag(device, AC.TAG_DIFF_POS)
                    elif self._net_matches(g_net, self.CircuitPorts.INPUT_NEGATIVE):
                        self.add_tag(device, AC.TAG_DIFF_NEG)

            # ------------------------ 4. 标记共模检测管 --------------------------
            if device.type in ["PMOS", "NMOS"]:
                g_net = device.terminals.get("G", "")
                if self._net_matches(g_net, self.CircuitPorts.COMMON_SIGN):
                    self.add_tag(device, AC.TAG_CM_OUTER)    

    # ------------------------------------------------ 标记输出管/频率补偿/RC共模检测 --------------------------------------------------------
    def _mark_outport_devices(self):
        """
        注意：根据预定义逻辑检测连接到输出端的 RC 结构，应用时应检查预定义逻辑是否匹配电路设计。

        MOS:D/S连接到输出端的MOS管标记为输出端管
        电容：输出端-电容-MOS栅：共模检测；输出端-电容-（单个纯电阻）-MOS S/D：频率补偿；输出端-电容-（单个纯电阻）-MOS栅与MOS S/D：频率补偿
        电阻：输出端-电阻-（单个纯电阻）-MOS栅：共模检测

        这里有很多冗余判断逻辑，需要优化

        **独立，不依赖其他函数**
        """
        AC = self.AC

        # --- 辅助函数 1: 获取二端器件的另一端网络 ---
        def _get_other_terminal_net(device: 'CircuitAnalyzer.Device', connected_net: str) -> Optional[str]:
            """获取电容/电阻的另一端网络名"""
            net1 = device.terminals.get("PLUS")
            net2 = device.terminals.get("MINUS")
            if not net1 or not net2: return None
            if self._net_matches(net1, {connected_net}): return net2
            elif self._net_matches(net2, {connected_net}): return net1
            return None

        # --- 辅助函数 2: 获取网络上的MOS管与对应连接方式---
        def _get_net_mos_connections(net: str, exclude_devices: Set[str]) -> List[Dict]:
            """
            获取指定网络上所有MOS管的连接信息。
            只关心MOS管，忽略其他器件。
            """
            if not net: return []
            mos_connections = []
            device_names_on_net = self.net_device_map.get(net.lower(), [])
            for dev_name in device_names_on_net:
                if dev_name in exclude_devices: continue
                dev = self.circuit.devices_dict.get(dev_name)
                if not dev or dev.type not in ["PMOS", "NMOS"]: continue
                if self._net_matches(dev.terminals.get("G", ""), {net}):
                    mos_connections.append({'conn_type': 'G', 'device': dev})
                else:
                    mos_connections.append({'conn_type': 'DS', 'device': dev})
            return mos_connections

        # --- 辅助函数 3: 检查网络是否只有单个电阻 ---
        def _get_net_single_resistor(net: str, exclude_devices: Set[str]) -> Optional['CircuitAnalyzer.Device']:
            """
            检查指定网络上是否 *仅* 包含一个电阻 (且无其他器件)。
            """
            if not net: return None
            devices_on_net = []
            device_names_on_net = self.net_device_map.get(net.lower(), [])
            for dev_name in device_names_on_net:
                if dev_name in exclude_devices: continue
                dev = self.circuit.devices_dict.get(dev_name)
                if dev: devices_on_net.append(dev)
            if len(devices_on_net) == 1 and devices_on_net[0].type == "Resistor":
                return devices_on_net[0]
            return None

        # --- 核心处理逻辑 ---
        def _process_output_net_devices(device_names: List[str], net_name: str):
            """
            处理连接到 *一个* 输出网络 (net_name) 上的所有器件 (device_names)。
            """
            for dev_name in device_names:
                device = self.circuit.devices_dict.get(dev_name)
                if not device: continue

                # --- 规则 0: MOS 输出端管 ---
                if device.type in ["PMOS", "NMOS"]:
                    is_s_conn = self._net_matches(device.terminals.get("S", ""), {net_name})
                    is_d_conn = self._net_matches(device.terminals.get("D", ""), {net_name})
                    
                    if net_name.lower() in positive_nets_lower:
                        if AC.TAG_OUTPORT_POS not in device.tags and (is_s_conn or is_d_conn):
                            self.add_tag(device, AC.TAG_OUTPORT_POS)
                    elif net_name.lower() in negative_nets_lower:
                        if AC.TAG_OUTPORT_NEG not in device.tags and (is_s_conn or is_d_conn):
                            self.add_tag(device, AC.TAG_OUTPORT_NEG)

                # --- 规则 1: 电容 (频率补偿/RC共模) ---
                elif device.type == "Capacitor":
                    cap_device = device
                    other_net = _get_other_terminal_net(cap_device, net_name)
                    if not other_net: continue

                    exclude_set = {cap_device.name}
                    mos_conns = _get_net_mos_connections(other_net, exclude_set)
                    num_mos = len(mos_conns)

                    if num_mos > 1:
                        self.add_tag(cap_device, AC.TAG_COMPENSATE)
                    elif num_mos == 1:
                        if mos_conns[0]['conn_type'] == 'G':
                            self.add_tag(cap_device, AC.TAG_RC_CM_DETECT)
                        else:
                            self.add_tag(cap_device, AC.TAG_COMPENSATE)
                    elif num_mos == 0:
                        serial_res = _get_net_single_resistor(other_net, exclude_set)
                        if serial_res:
                            far_net = _get_other_terminal_net(serial_res, other_net)
                            if not far_net: continue
                            exclude_set_far = {cap_device.name, serial_res.name}
                            mos_conns_far = _get_net_mos_connections(far_net, exclude_set_far)
                            
                            if len(mos_conns_far) > 1:
                                self.add_tag(cap_device, AC.TAG_COMPENSATE)
                                self.add_tag(serial_res, AC.TAG_COMPENSATE)
                            elif len(mos_conns_far) == 1:
                                if mos_conns_far[0]['conn_type'] != 'G':
                                    self.add_tag(cap_device, AC.TAG_COMPENSATE)
                                    self.add_tag(serial_res, AC.TAG_COMPENSATE)

                # --- 规则 2: 电阻 (RC共模) ---
                elif device.type == "Resistor":
                    res1_device = device
                    other_net = _get_other_terminal_net(res1_device, net_name)
                    if not other_net: continue

                    exclude_set = {res1_device.name}
                    mos_conns = _get_net_mos_connections(other_net, exclude_set)
                    
                    if len(mos_conns) == 1 and mos_conns[0]['conn_type'] == 'G':
                        self.add_tag(res1_device, AC.TAG_RC_CM_DETECT)
                    elif len(mos_conns) == 0:
                        serial_res2 = _get_net_single_resistor(other_net, exclude_set)
                        if serial_res2:
                            far_net = _get_other_terminal_net(serial_res2, other_net)
                            if not far_net: continue
                            mos_conns_far = _get_net_mos_connections(far_net, {res1_device.name, serial_res2.name})
                            
                            if len(mos_conns_far) == 1 and mos_conns_far[0]['conn_type'] == 'G':
                                self.add_tag(res1_device, AC.TAG_RC_CM_DETECT)
                                self.add_tag(serial_res2, AC.TAG_RC_CM_DETECT)

        # --- 主循环 ---
        positive_nets_lower = {n.lower() for n in self.CircuitPorts.OUTPORT_POSITIVE}
        for net_name_lower in positive_nets_lower:
            device_names = self.net_device_map.get(net_name_lower, [])
            _process_output_net_devices(device_names, net_name_lower)

        negative_nets_lower = {n.lower() for n in self.CircuitPorts.OUTPORT_NEGATIVE}
        for net_name_lower in negative_nets_lower:
            device_names = self.net_device_map.get(net_name_lower, [])
            _process_output_net_devices(device_names, net_name_lower)

    # ---------------------------------------------标记B型（4管）共模检测 ---------------------------------------------------
    ##################################################################################################################
    def _mark_common_mode_detect_b(self):
        """
        如果识别到2个外侧共模管，则查找其共源极连接的另外2个内侧共模管，并一并打上4管共模检测标签

        注意：假设存在2个外侧共模管时，必然有2个共源级连接内侧共模管，否则不打共模内侧管标签与4管共模检测标签

        **依赖外侧共模管标签**
        _mark_obvious_tags() 之后调用
        """
        AC = self.AC
        
        # 1. 从 Tag Index 获取外侧管
        outer_names = list(self.get_names_by_tag(AC.TAG_CM_OUTER))
        
        if len(outer_names) != 2:
            return

        try:
            dev1 = self.circuit.devices_dict[outer_names[0]]
            dev2 = self.circuit.devices_dict[outer_names[1]]

            s_net1 = dev1.terminals.get("S")
            s_net2 = dev2.terminals.get("S")
            
            # 检查源极是否连接到同一个网络
            if not s_net1 or s_net1 != s_net2:
                return
                
            common_s_net = s_net1
            
            # 查找连接到此共源极的所有器件
            all_devs_on_net = self.net_device_map.get(common_s_net.lower(), [])

            # 筛选出其他的 MOS 管
            other_mos_devices = []
            for name in all_devs_on_net:
                if name in outer_names:
                    continue
                    
                dev = self.circuit.devices_dict.get(name)
                # 检查是否为 MOS 且源极连接到共源点 (排除漏极连接的情况)
                if dev and dev.type in ["PMOS", "NMOS"] and self._net_matches(dev.terminals.get("S", ""), {common_s_net}):
                    other_mos_devices.append(dev)

            # 检查是否 *恰好* 存在另外两个MOS管 (构成4管结构)
            if len(other_mos_devices) == 2:
                all_four_devices = [dev1, dev2] + other_mos_devices

                # 标记内侧管
                self.add_tag(other_mos_devices[0], AC.TAG_CM_INNER)
                self.add_tag(other_mos_devices[1], AC.TAG_CM_INNER)
                
                # 标记所有成员为 4管共模检测成员
                for dev in all_four_devices:
                    self.add_tag(dev, AC.TAG_CM_4MOS)
                    
                # print(f"[Info] 识别到B型共模检测结构: {[d.name for d in all_four_devices]}")

        except KeyError:
            print("[Error] 共模检测识别中发现未登记的器件名称")
            pass

    ##########################################级联与普通电流镜标记#########################################################
    def _analyze_diode_mos_structures(self):
        """
        [重构版] 二极管结构分析
        
        逻辑：
        1. 找到所有二极管连接的 MOS (Master)。
        2. 找到所有栅极连接到 Master 的其他 MOS (Slaves)。
        3. 区分 Slaves 是“级联从管”还是“镜像管”。
        
        **依赖二极管连接标签**
        _mark_obvious_tags() 之后调用
        """
        groups = self._find_slave_mos_and_form_groups()
        for group in groups:
            self._mark_cascode_roles(group)
            self._mark_current_mirror_roles(group)

    def _find_slave_mos_and_form_groups(self) -> List[Dict]:
        """
        辅助函数：查找 Master-Slave 组
        """
        AC = self.AC
        groups = []
        # 使用 Tag Index 获取二极管
        masters_names = self.get_names_by_tag(AC.TAG_DIODE_MOS)
        
        for master_name in masters_names:
            master = self.circuit.devices_dict.get(master_name)
            if not master: continue

            g_net = master.terminals.get("G")
            if not g_net: continue

            slave_names = self.net_device_map.get(g_net.lower(), [])
            slaves = []
            for name in slave_names:
                if name == master.name: continue # 跳过自己

                device = self.circuit.devices_dict.get(name)
                if not device: continue
                if device.type not in ["PMOS", "NMOS"]: continue

                # 确认栅极确实连接
                if self._net_matches(device.terminals.get("G", ""), {g_net}):
                    slaves.append(device)

            groups.append({"master": master, "slaves": slaves, "g_net": g_net})

        return groups

    def _mark_cascode_roles(self, group: Dict):
        """
        辅助函数：标记级联关系 (Master -> Source connected Slave)
        """
        AC = self.AC
        master = group["master"]
        slaves = group["slaves"] # 注意：这是引用，列表内容会被修改
        
        current_s_net = master.terminals.get("S")
        cascode_slaves = []

        # 迭代查找级联链 (Master.S -> Slave1.D, Slave1.S -> Slave2.D ...)
        while slaves:
            # 在 slaves 中查找 D 端连接到 current_s_net 的管子
            found = next(
                (s for s in slaves if self._net_matches(s.terminals.get("D"), {current_s_net})),
                None
            )
            if not found:
                break
                
            # 标记
            self.add_tag(found, AC.TAG_CASCODE_SLAVE)
            cascode_slaves.append(found)
            
            # 更新搜索节点
            current_s_net = found.terminals.get("S")
            slaves.remove(found) # 从候选列表中移除，剩下的就是镜像管

        if cascode_slaves:
            self.add_tag(master, AC.TAG_CASCODE_MAIN)
            for slave in cascode_slaves:
                # [Relation] 记录级联关系
                self.add_relation(master.name, AC.REL_CASCODE_M2S, slave.name)
            
            # 登记子结构实例 (保持原有逻辑，这里可以登记)
            self.aggregate_substructure(AC.STR_CASCODE, [master] + cascode_slaves)

    def _mark_current_mirror_roles(self, group: Dict):
        """
        辅助函数：标记普通电流镜关系 (剩余的 Slaves)
        """
        AC = self.AC
        master = group["master"]
        # 排除已经被标记为级联从管的 (虽然 _mark_cascode_roles 已经 remove 了，但双重保险)
        remaining_slaves = [s for s in group["slaves"] if AC.TAG_CASCODE_SLAVE not in s.tags]
        
        if not remaining_slaves:
            return

        self.add_tag(master, AC.TAG_STD_MIRROR_REF)
        
        for slave in remaining_slaves:
            self.add_tag(slave, AC.TAG_STD_MIRROR_MIRROR)
            # [Relation] 记录普通电流镜关系
            self.add_relation(master.name, AC.REL_STD_REF2MIRROR, slave.name)
        
        # 子结构登记推迟到 _register_current_mirrors 统一处理

    ##################################################################################################################
    ##################################################################################################################
    # -----------------------------------------根参考管标记-------------------------------------------------
    def _mark_root_reference_path(self):
        """
        [重构版] 根参考管标记
        
        逻辑：
        从 IREF/IIN 端口出发，沿着二极管连接的 MOS 链向下查找，直到电源负端。
        路径上的所有 TAG_STD_MIRROR_REF 被追加标记为 TAG_ROOT_REF。
        
        **依赖普通电流镜参考管标签**
        _analyze_diode_mos_structures() 之后
        """
        AC = self.AC
        
        # 1. 查找起始网络 (IREF/IIN)
        start_net = None
        start_net_device_names = []
        current_source_lower = {s.lower() for s in self.CircuitPorts.CURRENT_SOURCE}

        for net_key in self.net_device_map.keys():
            if net_key in current_source_lower:
                start_net = net_key
                start_net_device_names = self.net_device_map[net_key]
                break 

        if not start_net:
            # print("信息：未找到电流源路径起始点 (IREF/IIN)。")
            return

        # 2. 查找起始器件 (必须是二极管连接的参考管)
        start_candidates = []
        for dev_name in start_net_device_names:
            dev = self.circuit.devices_dict.get(dev_name)
            # 检查 Tag Index 也可以，这里直接查对象 Tag
            if dev and (AC.TAG_DIODE_MOS in dev.tags and AC.TAG_STD_MIRROR_REF in dev.tags):
                start_candidates.append(dev)

        if len(start_candidates) != 1:
            # print(f"警告：电流源网络 '{start_net}' 未找到唯一根参考管 (找到 {len(start_candidates)} 个)。")
            return

        current_device = start_candidates[0]

        # 3. 循环遍历路径
        while current_device:
            # 再次校验
            if not (AC.TAG_DIODE_MOS in current_device.tags and AC.TAG_STD_MIRROR_REF in current_device.tags):
                break

            # 标记为根参考管
            self.add_tag(current_device, AC.TAG_ROOT_REF)

            # 4. 寻找下一级网络
            next_net = None
            if current_device.type == "NMOS":
                next_net = current_device.terminals.get("S")
            elif current_device.type == "PMOS":
                next_net = current_device.terminals.get("D")
            
            if not next_net or self._is_net_ground(next_net):
                break 

            # 5. 寻找下一级器件
            next_net_device_names = self.net_device_map.get(next_net.lower(), [])
            candidates = []
            for dev_name in next_net_device_names:
                if dev_name == current_device.name: continue

                dev = self.circuit.devices_dict.get(dev_name)
                if dev and (AC.TAG_DIODE_MOS in dev.tags and AC.TAG_STD_MIRROR_REF in dev.tags):
                    candidates.append(dev)

            if len(candidates) == 1:
                current_device = candidates[0]
            else:
                # 分叉或中断，停止搜索
                break

    #################################################低压电流镜标记######################################################
    ##################################################################################################################
    def _detect_low_voltage_current_mirrors(self):
        """
        A的D连B的G，A的S连B的D：A为上层参考管，B为下层参考管
        A的G连B的D，A的D连B的S：B为上层参考管，A为下层参考管
        以下层参考管为中心，构建对上层参考管、上层偏置管、上层镜像管、下层镜像管的关系，组成低压电流镜

        注意：假设偏置管最多只有一个；不考虑电阻、电容等其他器件；基于普通电流镜识别偏置管，随后删除耦合的普通电流镜标签与缓存
        **依赖二极管标签、普通电流镜镜像管标签**
        _mark_obvious_tags() 之后
        _analyze_diode_mos_structures之后
        """
        AC = self.AC
        mos_devices = [d for d in self.circuit.devices_dict.values() if d.type in ["PMOS", "NMOS"]]
        processed_mos = set()

        # 预构建栅极映射加速查找
        gate_net_map: DefaultDict[str, Set['CircuitAnalyzer.Device']] = defaultdict(set)
        for mos in mos_devices:
            g_net = mos.terminals.get("G")
            if g_net:
                gate_net_map[g_net.lower()].add(mos)

        for a in mos_devices:
            a_name = a.name
            if a_name in processed_mos: continue

            a_g = a.terminals.get("G")
            a_d = a.terminals.get("D")
            a_s = a.terminals.get("S")
            if not (a_g and a_d and a_s): continue

            # 优化：只检查连接到 A.D 或 A.G 的器件
            candidate_b_names = set()
            if a_d: candidate_b_names.update(self.net_device_map.get(a_d.lower(), []))
            if a_g: candidate_b_names.update(self.net_device_map.get(a_g.lower(), []))

            for b_name in candidate_b_names:
                if b_name == a_name or b_name in processed_mos: continue
                
                b = self.circuit.devices_dict.get(b_name)
                if not b or b.type not in ["PMOS", "NMOS"]: continue

                b_g = b.terminals.get("G")
                b_d = b.terminals.get("D")
                b_s = b.terminals.get("S")
                if not (b_g and b_d and b_s): continue

                # Case 1: B.G=A.D, B.D=A.S (且非自馈 B.G!=A.G) -> A=Upper, B=Lower
                if self._net_matches(b_g, {a_d}) and self._net_matches(b_d, {a_s}) and not self._net_matches(b_g, {a_g}):
                    self.add_tag(a, AC.TAG_LV_UPPER_REF)
                    self.add_tag(b, AC.TAG_LV_LOWER_REF)
                    processed_mos.add(a_name)
                    processed_mos.add(b_name)
                    self._mark_low_voltage_mirrors(a, b, gate_net_map)
                    break

                # Case 2: B.D=A.G, B.S=A.D -> B=Upper, A=Lower
                if self._net_matches(b_d, {a_g}) and self._net_matches(b_s, {a_d}) and not self._net_matches(b_g, {a_g}):
                    self.add_tag(b, AC.TAG_LV_UPPER_REF)
                    self.add_tag(a, AC.TAG_LV_LOWER_REF)
                    processed_mos.add(a_name)
                    processed_mos.add(b_name)
                    self._mark_low_voltage_mirrors(b, a, gate_net_map)
                    break

    #################################################低压电流镜标记######################################################
    ##################################################################################################################
    def _mark_low_voltage_mirrors(self, upper_ref: 'CircuitAnalyzer.Device', lower_ref: 'CircuitAnalyzer.Device',
                                  gate_net_map):
        """
        标记低压电流镜的镜像管
        """
        AC = self.AC
        upper_ref_g = upper_ref.terminals["G"]
        lower_ref_g = lower_ref.terminals["G"]

        upper_bias = None
        upper_mirrors_list = []

        # 1. 检查上层是否“耦合”了普通电流镜结构 (即 UpperRef 本身是某个 Diode 的镜像)
        # 这通常意味着存在一个 Diode connected MOS 提供偏置
        if AC.TAG_STD_MIRROR_MIRROR in upper_ref.tags:
            devices_on_gate = gate_net_map.get(upper_ref_g.lower(), set())
            diode_mos_list = [d for d in devices_on_gate if AC.TAG_DIODE_MOS in d.tags]

            if diode_mos_list:
                upper_bias = diode_mos_list[0]
                self.add_tag(upper_bias, AC.TAG_LV_UPPER_BIAS)
            else:
                print(f"[Warning] LV Ref {upper_ref.name} 有镜像标签但无 Diode 偏置。")
                # 这种情况可能需要降级处理或报错，保持原逻辑继续执行

        # 2. 标记上层镜像管 (Upper Mirrors)
        all_upper_on_gate = gate_net_map.get(upper_ref_g.lower(), set())
        for mos in all_upper_on_gate:
            if mos.name == upper_ref.name: continue
            if upper_bias and mos.name == upper_bias.name: continue

            self.add_tag(mos, AC.TAG_LV_UPPER_MIRROR)
            upper_mirrors_list.append(mos)

        # 3. 标记下层镜像管 (Lower Mirrors)
        all_lower_on_gate = gate_net_map.get(lower_ref_g.lower(), set())
        lower_mirrors_list = []
        for mos in all_lower_on_gate:
            if mos.name == lower_ref.name: continue
            
            self.add_tag(mos, AC.TAG_LV_LOWER_MIRROR)
            lower_mirrors_list.append(mos)

        if upper_mirrors_list and lower_mirrors_list:
            # --- 净化逻辑 (Purge) ---
            # 如果 UpperBias 之前被识别为普通电流镜参考管，现在它属于 LV 结构的一部分，
            # 我们需要移除它与镜像管（现在是 LV 上层镜像管）之间的普通电流镜关系，
            # 避免双重约束冲突。
            if upper_bias:
                # 检查并清理 upper_bias 作为 REF 的关系
                # 注意：我们之前存的是 REL_STD_REF2MIRROR
                old_mirrors = self.get_relations(upper_bias.name, AC.REL_STD_REF2MIRROR)
                
                if old_mirrors:
                    # print(f"  [净化] 清除 {upper_bias.name} 的普通电流镜关系，归入 LV 结构...")
                    
                    # 1. 移除镜像管的 STD 标签
                    for m_name in old_mirrors:
                        self.remove_tag(m_name, AC.TAG_STD_MIRROR_MIRROR)
                    
                    # 2. 移除自己的 STD REF 标签
                    self.remove_tag(upper_bias, AC.TAG_STD_MIRROR_REF)
                    
                    # 3. 从关系图中彻底删除该条目
                    if AC.REL_STD_REF2MIRROR in self.relation_graph[upper_bias.name]:
                        del self.relation_graph[upper_bias.name][AC.REL_STD_REF2MIRROR]

            # --- 建立 LV 关系 (以 Lower Ref 为锚点) ---
            self.add_relation(lower_ref.name, AC.REL_LV_LREF2UREF, upper_ref.name)
            
            if upper_bias:
                self.add_relation(lower_ref.name, AC.REL_LV_LREF2UBIAS, upper_bias.name)
            
            # 将所有 Token (上层+下层镜像管) 挂载到 Lower Ref
            all_tokens = upper_mirrors_list + lower_mirrors_list
            for m in all_tokens:
                self.add_relation(lower_ref.name, AC.REL_LV_LREF2TOKEN, m.name)

    # -----------------------------------------------------电流路径生成-----------------------------------------------------------
    def generate_current_paths(self):
        """
        电流路径形式：
        1.电源正端-NMOS/电阻-(NMOS/电阻)……-电源负端
        2.电源正端-PMOS/电阻-(PMOS/电阻)……-(NMOS/电阻)……-电源负端
        
        注意：仅包含MOS管和电阻；严格禁止 NMOS -> PMOS 的逆向连接；两个MOS管之间最多只能有2个电阻，否则无法识别成电流路径

        **依赖识别出的顶层节点**
        _mark_obvious_tags() 之后
        """
        all_paths: List[List[str]] = []

        # 内部 DFS 函数
        def dfs(current_dev: 'CircuitAnalyzer.Device', current_path: List[str], incoming_net: str = ""):
            # 1. 环路检测
            if current_dev.name in current_path[::2]:
                return

            # 2. 加入当前路径
            new_path_with_dev = current_path + [current_dev.name]

            # 3. 获取流出网络
            out_net = self._get_device_output_net(current_dev, incoming_net)
            if not out_net:
                return 

            # 4. 终止条件判断 (到达地)
            if self._is_net_ground(out_net):
                all_paths.append(new_path_with_dev + [out_net])
                return

            # 5. 寻找下一级器件
            # 必须传入 current_dev 以便进行父节点类型校验 (如 NMOS 不接 PMOS)
            next_devices = self._find_valid_next_devices(out_net, current_dev)
            
            if not next_devices:
                return 

            # 6. 递归
            path_to_pass = new_path_with_dev + [out_net]
            for next_dev in next_devices:
                dfs(next_dev, path_to_pass, incoming_net=out_net)

        # --- 主循环 ---
        if not self.top_nodes:
            print("警告: 未识别到顶层节点，无法生成电流路径。")
            return

        for node in self.top_nodes:
            # 特殊处理：顶层电阻校验
            if node.type == "Resistor":
                power_net = next((net for net in node.terminals.values() if self._is_net_power(net)), None)
                # 顶层电阻视为父节点是 POWER
                if power_net:
                    if not self._check_resistor_validity(node, power_net, "POWER"):
                        continue 

            dfs(node, [], incoming_net="")

        self.circuit.current_paths = all_paths
        print(f"信息: 生成了 {len(all_paths)} 条电流路径。")

    # ------------------------------
    # 辅助方法：寻找有效的下一级器件 
    # ------------------------------
    def _find_valid_next_devices(self, net_name: str, parent_dev: 'CircuitAnalyzer.Device') -> List['CircuitAnalyzer.Device']:
        """
        在 net_name 上寻找下一级器件。
        规则：
        1. 排除自己。
        2. NMOS -> PMOS 是非法路径 (禁止)。
        3. NMOS -> NMOS(D) 合法。
        4. PMOS -> PMOS(S) / NMOS(D) 合法。
        5. Resistor 需进行 Look-ahead 校验)(实际是校验NMOS/PMOS连接合法性)。
        """
        candidates = []
        device_names_on_net = self.net_device_map.get(net_name.lower(), [])
        
        parent_type = parent_dev.type

        for name in device_names_on_net:
            if name == parent_dev.name: continue
            
            dev = self.circuit.devices_dict.get(name)
            if not dev: continue

            is_valid = False
            
            # --- Case 1: 下一级是 NMOS ---
            if dev.type == "NMOS":
                # 无论父节点是 PMOS/NMOS/Res，下一级 NMOS 必须漏极 (D) 输入
                if self._net_matches(dev.terminals.get("D", ""), {net_name}):
                    is_valid = True
            
            # --- Case 2: 下一级是 PMOS ---
            elif dev.type == "PMOS":
                # [修正逻辑]: 如果父节点是 NMOS，禁止连接到 PMOS
                if parent_type == "NMOS":
                    is_valid = False
                else:
                    # 父节点是 PMOS 或 Resistor(且经过校验)
                    # PMOS 必须源极 (S) 输入 (例如 Cascode)
                    if self._net_matches(dev.terminals.get("S",""), {net_name}):
                        is_valid = True
            
            # --- Case 3: 下一级是 Resistor ---
            elif dev.type == "Resistor":
                # 必须进行“前瞻校验”
                if self._check_resistor_validity(dev, net_name, parent_type):
                    is_valid = True

            if is_valid:
                candidates.append(dev)
        
        return candidates

    # ------------------------------
    # 辅助方法：电阻连接规则校验（防止NMOS后接PMOS）
    # ------------------------------
    def _check_resistor_validity(self, resistor: 'CircuitAnalyzer.Device', input_net: str, parent_type: str) -> bool:
        """
        检查电阻的有效性（实质是检查NMOS/PMOS连接合法性）。
        逻辑：Parent -> Resistor(input) -> Resistor(target) -> Target Devices
        
        校验规则：
        1. POWER -> Res -> NMOS(D) / PMOS(S) / GND
        2. NMOS  -> Res -> NMOS(D) / GND  (禁止 PMOS)
        3. PMOS  -> Res -> NMOS(D) / PMOS(S) / GND
        """
        # 1. 获取电阻另一端
        target_net = self._get_device_output_net(resistor, input_net)
        if not target_net: return False

        # 2. 接地总是合法的
        if self._is_net_ground(target_net):
            return True

        # 3. 检查 Target Net 上的器件
        devices_on_target = self.net_device_map.get(target_net.lower(), [])

        for name in devices_on_target:
            if name == resistor.name: continue
            target_dev = self.circuit.devices_dict.get(name)
            if not target_dev: continue

            # 规则：如果上级是 NMOS，下级只能是 NMOS(D) 或 GND，绝不能是 PMOS
            if parent_type == "NMOS":
                if target_dev.type == "NMOS" and self._net_matches(target_dev.terminals.get("D", ""), {target_net}):
                    return True
                # PMOS is invalid here
            
            # 规则：如果上级是 PMOS/POWER，下级可以是 NMOS(D) 或 PMOS(S)
            else: 
                if target_dev.type == "NMOS" and self._net_matches(target_dev.terminals.get("D", ""), {target_net}):
                    return True
                elif target_dev.type == "PMOS" and self._net_matches(target_dev.terminals.get("S", ""), {target_net}):
                    return True
            
        return False

    # ------------------------------
    # 辅助方法：获取器件流出网络
    # ------------------------------
    def _get_device_output_net(self, device: 'CircuitAnalyzer.Device', incoming_net: str = "") -> Optional[str]:
        if device.type == "NMOS":
            return device.terminals.get("S")
        elif device.type == "PMOS":
            return device.terminals.get("D")
        elif device.type == "Resistor":
            net1 = device.terminals.get("PLUS", "")
            net2 = device.terminals.get("MINUS", "")
            if incoming_net:
                if self._net_matches(net1, {incoming_net}): return net2
                if self._net_matches(net2, {incoming_net}): return net1
            else:
                is_net1_pwr = self._is_net_power(net1)
                is_net2_pwr = self._is_net_power(net2)
                if is_net1_pwr: return net2
                if is_net2_pwr: return net1
        return None

    # --------------------------------------------------电流束生成、电流束路径生成、电流束网络生成、电流束管标记---------------------------------------------------
    def analyze_current_beams(self):
        """
        根据定义的规则获取电流束。使用 [Dev, Net, Dev] 格式，并提取电流束内部网络集合与电流束内部按位置索引的器件集合
        注意：默认偏置电路不会形成电流束
        
        电流束获取规则优先级顺序：
        1. 包含4管共模检测 (CMFB)的电流路径为一类电流束
        2. 除掉共模检测，包含差分输入对的电流路径为一类电流束
        3. 除掉共模检测与输入，包含输出端管的电流路径为一类电流束
        4. 除掉共模检测、输入、输出端管，包含输出管栅极网络的长度相等的电流路径为一类电流束
        5. 除掉以上4个，包含公共器件的长度相等的电流路径为一类电流束
        6. 剩余路径不归类。

        **依赖4管共模检测标签、差分输入标签、输出端管标签、电流路径生成**
        _mark_obvious_tags()之后
        _mark_outport_devices()之后
        _mark_common_mode_detect_b() 之后
        generate_current_paths() 之后
        """
        AC = self.AC

        # 0. 确保电流路径已生成
        if not self.circuit.current_paths:
            print("警告：电流路径未生成，请先调用 generate_current_paths()")
            return

        # 复制一份路径列表，以便安全地从中移除
        remaining_paths: Set[tuple] = {tuple(path) for path in self.circuit.current_paths}
        beams: Dict[str, List[List[str]]] = {}

        # =====================================================
        # 规则 1: 4管共模检测 (优先级最高)
        # =====================================================
        # 获取所有标记为 COMMON_4MOS 的器件名称
        cmfb_devices = self.get_names_by_tag(AC.TAG_CM_4MOS)
        beam1_paths: Set[tuple] = set()

        if cmfb_devices:
            for path in remaining_paths:
                path_devs = path[::2]
                # 只要路径中包含任意一个 CMFB 器件，该路径即归属 CMFB 束
                if any(d in cmfb_devices for d in path_devs):
                    beam1_paths.add(path)

        if beam1_paths:
            beams["beam_1_cmfb"] = [list(p) for p in beam1_paths]
            remaining_paths -= beam1_paths

        # =====================================================
        # 规则 2: 差分输入对
        # =====================================================
        diff_pos = self.get_names_by_tag(AC.TAG_DIFF_POS)
        diff_neg = self.get_names_by_tag(AC.TAG_DIFF_NEG)
        beam2_devices = diff_pos | diff_neg
        beam2_paths: Set[tuple] = set()

        if beam2_devices:
            for path in remaining_paths:
                path_devs = path[::2]
                if any(d in beam2_devices for d in path_devs):
                    beam2_paths.add(path)

        if beam2_paths:
            beams["beam_2_differential"] = [list(p) for p in beam2_paths]
            remaining_paths -= beam2_paths

        # =====================================================
        # 规则 3: 输出端管
        # =====================================================
        out_pos = self.get_names_by_tag(AC.TAG_OUTPORT_POS)
        out_neg = self.get_names_by_tag(AC.TAG_OUTPORT_NEG)
        beam3_devices = out_pos | out_neg
        beam3_paths: Set[tuple] = set()

        if beam3_devices:
            for path in remaining_paths:
                path_devs = path[::2]
                if any(device_name in beam3_devices for device_name in path_devs):
                    beam3_paths.add(path)

        if beam3_paths:
            beams["beam_3_output"] = [list(p) for p in beam3_paths]
            remaining_paths -= beam3_paths

        # =====================================================
        # 规则 4: 输出管栅极关联路径 
        # =====================================================
        # 4a. 找出所有输出管的栅极网络
        out_gate_nets: Set[str] = set()
        # 注意：这里重新获取一次输出管集合，逻辑上是正确的
        all_out_devices = out_pos | out_neg
        
        for dev_name in all_out_devices:
            device = self.circuit.devices_dict.get(dev_name)
            if device:
                g_net = device.terminals.get("G")
                if g_net:
                    out_gate_nets.add(g_net)

        # 4b. 找出连接到这些栅极网络的所有器件，没有排除自身，因为电流路径不会连接到栅极
        devices_on_out_g_nets: Set[str] = set()
        if out_gate_nets:
            for net in out_gate_nets:
                devices_on_out_g_nets.update(self.net_device_map.get(net.lower(), []))

        beam4_candidates: Set[tuple] = set()
        if devices_on_out_g_nets:
            # 4c. 找出剩余路径中，包含这些“栅极关联器件”的路径
            for path in remaining_paths:
                path_device_set = set(path[::2])
                if not path_device_set.isdisjoint(devices_on_out_g_nets):
                    beam4_candidates.add(path)

        # 4d. 按长度分组
        grouped_by_length_beam4: DefaultDict[int, List[List[str]]] = defaultdict(list)
        for path in beam4_candidates:
            grouped_by_length_beam4[len(path[::2])].append(list(path))

        # 4e. 登记为束
        beam4_idx = 1
        paths_to_remove_for_beam4: Set[tuple] = set()
        for length, path_list in grouped_by_length_beam4.items():
            if len(path_list) > 1:
                beams[f"beam_4_out_gate_len{length}_group{beam4_idx}"] = path_list
                paths_to_remove_for_beam4.update(tuple(p) for p in path_list)
                beam4_idx += 1

        remaining_paths -= paths_to_remove_for_beam4

        # =====================================================
        # 规则 5: 公共器件索引匹配
        # =====================================================
        # 5a. 按长度分组
        remaining_grouped_by_length: DefaultDict[int, List[tuple]] = defaultdict(list)
        for path_tuple in remaining_paths:
            remaining_grouped_by_length[len(path_tuple[::2])].append(path_tuple)

        beam5_idx = 1
        paths_to_remove_for_beam5: Set[tuple] = set()

        for length, paths in remaining_grouped_by_length.items():
            if len(paths) <= 1:
                continue

            # 并查集初始化
            parent = list(range(len(paths)))

            def find_set(i):
                if parent[i] == i:
                    return i
                parent[i] = find_set(parent[i])
                return parent[i]

            def unite_sets(i, j):
                root_i = find_set(i)
                root_j = find_set(j)
                if root_i != root_j:
                    parent[root_i] = root_j

            # 5b. 比较路径对
            for i in range(len(paths)):
                for j in range(i + 1, len(paths)):
                    path_i_devs = paths[i][::2]
                    path_j_devs = paths[j][::2]

                    has_common_indexed_device = False
                    for k in range(length):
                        # 严格比较同一索引位置的器件名称
                        if path_i_devs[k] == path_j_devs[k]:
                            has_common_indexed_device = True
                            break

                    if has_common_indexed_device:
                        unite_sets(i, j)

            # 5c. 构建最终组
            final_groups: DefaultDict[int, List[List[str]]] = defaultdict(list)
            for i in range(len(paths)):
                root = find_set(i)
                final_groups[root].append(list(paths[i]))

            # 5d. 登记
            for group_paths in final_groups.values():
                if len(group_paths) > 1:
                    beams[f"beam_5_common_dev_len{length}_group{beam5_idx}"] = group_paths
                    paths_to_remove_for_beam5.update(tuple(p) for p in group_paths)
                    beam5_idx += 1

        remaining_paths -= paths_to_remove_for_beam5

        # =====================================================
        # 后处理：提取内部网络、生成索引路径、打标签
        # =====================================================
        # 1. 提取所有束的内部导线网络
        for beam_id, paths_list in beams.items():
            for path in paths_list:
                # 提取 path 中的 Net (奇数索引)
                nets_in_path = path[1::2]
                self.circuit.beam_net_sets[beam_id].update(nets_in_path)

        # 2. 生成电流束路径 (List[Set[str]]) 并存储
        beam_paths_result: Dict[str, List[Set[str]]] = {}
        for beam_id, paths_list in beams.items():
            if not paths_list:
                continue

            # 获取最大长度 (同一束通常长度一致)
            max_len = 0
            for p in paths_list:
                path_devs = p[::2]
                if len(path_devs) > max_len:
                    max_len = len(path_devs)

            # 按索引生成器件集合
            current_beam_path: List[Set[str]] = []
            for i in range(max_len):
                index_set: Set[str] = set()
                for path in paths_list:
                    path_devs = path[::2]
                    if i < len(path_devs):
                        dev_name = path_devs[i]
                        index_set.add(dev_name)
                        
                        # [Refactor] 使用标准接口打标签
                        self.add_tag(dev_name, AC.TAG_IN_CURRENT_BEAM)
                
                current_beam_path.append(index_set)

            beam_paths_result[beam_id] = current_beam_path

        # 3. 存储结果
        self.circuit.current_beam_paths = beam_paths_result
        self.circuit.current_beams = beams

    ##############################################偏置管标记################################################################
    def _mark_bias_mirrors(self):
        """
        默认参考管在主电路中时，不会有镜像管处在偏置电路中；默认偏置电路不会形成电流束
        普通电流镜：参考管在偏置电路，所有不在电流束中的镜像管标记为 BIAS。参考管在主电路，跳过。
        低压电流镜：下层参考管在偏置电路，所有不在电流束中的镜像管标记为 BIAS。下层参考管在主电路，跳过。

        **要在标记根参考管、识别低压电流镜、分析电流束后调用**
        _mark_root_reference_path之后
        _detect_low_voltage_current_mirrors之后
        analyze_current_beams之后
        """
        AC = self.AC
        # --- 1. 处理普通电流镜 ---
        # 获取所有普通电流镜参考管
        ref_names = self.get_names_by_tag(AC.TAG_STD_MIRROR_REF)
        
        for ref_name in ref_names:
            ref_dev = self.circuit.devices_dict.get(ref_name)
            if not ref_dev: continue

            # 如果参考管在电流束中 (即主信号通路)，跳过
            if AC.TAG_IN_CURRENT_BEAM in ref_dev.tags:
                continue

            # 获取所有镜像管
            mirrors = self.get_relations(ref_name, AC.REL_STD_REF2MIRROR)
            is_root = AC.TAG_ROOT_REF in ref_dev.tags
            
            for m_name in mirrors:
                m_dev = self.circuit.devices_dict.get(m_name)
                if not m_dev: continue

                # 如果镜像管也不在电流束中 -> 确认为偏置用途
                if AC.TAG_IN_CURRENT_BEAM not in m_dev.tags:
                    self.add_tag(m_dev, AC.TAG_STD_MIRROR_BIAS)
                    
                    # 如果是 Root Ref，记录特殊的 Bias 关系 (用于参数互锁)
                    if is_root:
                        self.add_relation(ref_name, AC.REL_STD_ROOT2BIAS, m_name)

        # --- 2. 处理低压电流镜 ---
        # 获取所有低压电流镜下层参考管
        lower_ref_names = self.get_names_by_tag(AC.TAG_LV_LOWER_REF)
        
        for lower_ref_name in lower_ref_names:
            lower_ref_dev = self.circuit.devices_dict.get(lower_ref_name)
            if not lower_ref_dev: continue

            # 如果 Lower Ref 在电流束中，跳过
            if AC.TAG_IN_CURRENT_BEAM in lower_ref_dev.tags:
                continue

            # 获取所有关联的镜像管 (Token)
            mirror_names = self.get_relations(lower_ref_name, AC.REL_LV_LREF2TOKEN)
            
            for m_name in mirror_names:
                m_dev = self.circuit.devices_dict.get(m_name)
                if not m_dev: continue

                # 标记不在电流束中的镜像管
                if AC.TAG_IN_CURRENT_BEAM not in m_dev.tags:
                    self.add_tag(m_dev, AC.TAG_LV_BIAS_MIRROR)

    # -------------------------------------------------子结构实例检测与登记----------------------------------------------------------
    # 函数识别顺序需要优化以提高代码效率
    def _register_beam_substructures(self):
        """
        对于所有电流束，按顺序遍历电流束路径元素（器件列表）
        元素长度为4：1.处理4管共模检测，依据4管共模检测标签；2.处理典型负载，依赖4管共栅
        元素长度非4（2,4）：1.处理差分输入，依据差分输入标签；2.处理输出端管，依据输出端管标签；
        3.处理A型负载，依据二极管标签与普通电流镜标签；4.处理B型负载，依据二极管标签；5.处理典型负载，依据普通电流镜标签
        6.处理2管共模检测情况，找到内侧共模管并打上2管共模检测标签；7.处理栅极处在至少一个电流束内部网络集合中的器件对，登记为跨束栅极连接结构

        注意：1.先单独处理4管共模检测与4管共栅是为了避免错误，这两部分顺序可换。4管共模检测实际可以在打标签时登记；2.差分输入、输出端实际上可以在之前打标签的时候进行登记；
        3.元素长度非4实际是指长度为2或4，4在现有逻辑中特指7与5的结合（即典型负载与跨束连接结构），因为现有的逻辑只能处理这两种长度；
        4.A型负载、B型负载、2管共模检测、跨束连接的顺序可换，典型负载顺序在A型负载之后。但在典型负载逻辑中加入二极管标签逻辑，即可与A型负载的识别解耦合
        """
        AC = self.AC

        def _register_helper(members: List['CircuitAnalyzer.Device'], sub_key: str, group_key: str):
            if not members: return
            # 登记到 device_groups (方便后续查询，如 _get_tail_current)
            self.add_group(group_key, [d.name for d in members])
            # 登记子结构实例 (生成约束)
            self.aggregate_substructure(sub_key, members)

        # --- 辅助函数 ---
        def _check_cross_beam_symmetry(mos_a: 'CircuitAnalyzer.Device',
                                       mos_b: 'CircuitAnalyzer.Device') -> bool:  #
            """
                检查两个MOS管的栅极网络是否至少在某一个电流束的 *内部网络* 集合中。
            """
            g_net_a = mos_a.terminals.get("G")
            g_net_b = mos_b.terminals.get("G")

            if not g_net_a or not g_net_b:
                return False

            # 遍历在 analyze_current_beams 中生成的网络集合
            for beam_net_set in self.circuit.beam_net_sets.values():
                if self._net_matches(g_net_a, beam_net_set) and self._net_matches(g_net_b, beam_net_set):
                    return True  # 匹配成功

            return False

        # --- 构建镜像管 -> 参考管 的反向查找字典 ---
        mirror_to_ref_map: Dict[str, str] = {}
        # (A) 普通电流镜
        for ref_name in self.relation_graph:
            if AC.REL_STD_REF2MIRROR in self.relation_graph[ref_name]:
                for m_name in self.relation_graph[ref_name][AC.REL_STD_REF2MIRROR]:
                    mirror_to_ref_map[m_name] = ref_name
        
        # (B) 低压电流镜 (Token 均指向 Lower Ref)
        for lower_ref_name in self.relation_graph:
            if AC.REL_LV_LREF2TOKEN in self.relation_graph[lower_ref_name]:
                for m_name in self.relation_graph[lower_ref_name][AC.REL_LV_LREF2TOKEN]:
                    mirror_to_ref_map[m_name] = lower_ref_name

        # --- 主循环：遍历所有唯一的“对” ---
        processed_devices: Set[str] = set()
        processed_4_devices: Set[str] = set()  # 用于4器件结构

        for beam_path in self.circuit.current_beam_paths.values():
            # beam_path 是 [Set[Dev], Set[Dev], ...]
            # 我们需要获取 *器件* 集合

            for element_set_names in beam_path:
                # ---优先处理 4-器件结构，避免逻辑错误 ---
                if len(element_set_names) == 4:
                    if any(element in processed_4_devices for element in element_set_names):
                        continue  # 已处理过

                    try:
                        members = [self.circuit.devices_dict[name] for name in element_set_names]
                    except KeyError:
                        continue  # 器件不存在

                    # 规则 1: 4管共模检测
                    if all(AC.TAG_CM_4MOS in d.tags for d in members):
                        _register_helper(members, AC.STR_CM_DETECT_B, AC.STR_CM_DETECT_B)
                        processed_4_devices.update(element_set_names)
                        continue

                    # 规则 2: 典型负载 (基于栅极连接)
                    g_net_groups: DefaultDict[str, List['CircuitAnalyzer.Device']] = defaultdict(list)  #
                    for d in members:
                        g_net = d.terminals.get("G")
                        if g_net:
                            g_net_groups[g_net].append(d)

                    unique_g_nets = len(g_net_groups)

                    if unique_g_nets == 1:
                        # 所有 4 个栅极相连
                        for d in members: self.add_tag(d, AC.TAG_LOAD_TYP)
                        _register_helper(members, AC.STR_LOAD_TYPICAL, AC.STR_LOAD_TYPICAL)
                        processed_4_devices.update(element_set_names)
                        continue

                # --- 处理所有器件对 ---
                if len(element_set_names) >= 2:
                    # 使用 itertools.combinations 遍历所有唯一的对
                    for dev_a_name, dev_b_name in itertools.combinations(element_set_names, 2):
                        if dev_a_name in processed_devices or dev_b_name in processed_devices:
                            continue  # 已处理过相关器件
                        try:
                            dev_a = self.circuit.devices_dict[dev_a_name]
                            dev_b = self.circuit.devices_dict[dev_b_name]
                        except KeyError:
                            continue  # 器件不存在
                        # 只处理 MOS 对
                        if dev_a.type not in ["PMOS", "NMOS"] or dev_b.type not in ["PMOS", "NMOS"]:
                            continue

                        members = [dev_a, dev_b]

                        # --- 特殊或G连接的器件对 ---
                        # 规则 1: 差分输入对
                        is_diff = (AC.TAG_DIFF_POS in dev_a.tags and AC.TAG_DIFF_NEG in dev_b.tags) or \
                                  (AC.TAG_DIFF_NEG in dev_a.tags and AC.TAG_DIFF_POS in dev_b.tags)
                        if is_diff:
                            _register_helper(members, AC.STR_DIFF_PAIR, AC.STR_DIFF_PAIR)
                            processed_devices.update([dev_a_name, dev_b_name])
                            continue

                        # 规则 2: 输出端对
                        is_out = (AC.TAG_OUTPORT_POS in dev_a.tags and AC.TAG_OUTPORT_NEG in dev_b.tags) or \
                                 (AC.TAG_OUTPORT_NEG in dev_a.tags and AC.TAG_OUTPORT_POS in dev_b.tags)
                        if is_out:
                            _register_helper(members, AC.STR_OUTPORT_PAIR, AC.STR_OUTPORT_PAIR)
                            processed_devices.update([dev_a_name, dev_b_name])
                            continue

                        # 规则 3: A型负载 (二极管 + 镜像管)
                        a_is_diode = AC.TAG_DIODE_MOS in dev_a.tags
                        b_is_diode = AC.TAG_DIODE_MOS in dev_b.tags
                        
                        # 检查镜像关系 (利用 Relation Graph)
                        # Case A: A is Diode (Ref), B is Mirror
                        a_mirrors = self.get_relations(dev_a_name, AC.REL_STD_REF2MIRROR)
                        is_a_ref_b = dev_b_name in a_mirrors
                        
                        # Case B: B is Diode (Ref), A is Mirror
                        b_mirrors = self.get_relations(dev_b_name, AC.REL_STD_REF2MIRROR)
                        is_b_ref_a = dev_a_name in b_mirrors

                        if a_is_diode and is_a_ref_b:
                            self.add_tag(dev_a, AC.TAG_LOAD_A_DIO)
                            self.add_tag(dev_b, AC.TAG_LOAD_A_TYP)
                            _register_helper(members, AC.STR_LOAD_A, AC.STR_LOAD_A)
                            processed_devices.update([dev_a_name, dev_b_name])
                            continue
                        elif b_is_diode and is_b_ref_a:
                            self.add_tag(dev_b, AC.TAG_LOAD_A_DIO)
                            self.add_tag(dev_a, AC.TAG_LOAD_A_TYP)
                            _register_helper(members, AC.STR_LOAD_A, AC.STR_LOAD_A)
                            processed_devices.update([dev_a_name, dev_b_name])
                            continue

                        # 规则 5: 典型负载 (来自电流镜)
                        ref_a = mirror_to_ref_map.get(dev_a_name)
                        ref_b = mirror_to_ref_map.get(dev_b_name)
                                                      
                        if ref_a and ref_b and ref_a == ref_b:
                            self.add_tag(dev_a, AC.TAG_LOAD_TYP)
                            self.add_tag(dev_b, AC.TAG_LOAD_TYP)
                            _register_helper(members, AC.STR_LOAD_TYPICAL, AC.STR_LOAD_TYPICAL)
                            processed_devices.update([dev_a_name, dev_b_name])
                            continue

                        # 规则 6: 共模检测A
                        a_is_outer = AC.TAG_CM_OUTER in dev_a.tags
                        b_is_outer = AC.TAG_CM_OUTER in dev_b.tags
                        
                        if a_is_outer != b_is_outer: # XOR
                            self.add_tag(dev_a, AC.TAG_CM_2MOS)
                            self.add_tag(dev_b, AC.TAG_CM_2MOS)
                            
                            inner = dev_b if a_is_outer else dev_a
                            self.add_tag(inner, AC.TAG_CM_INNER)
                            
                            _register_helper(members, AC.STR_CM_DETECT_A, AC.STR_CM_DETECT_A)
                            processed_devices.update([dev_a_name, dev_b_name])
                            continue

                        # --- 非 G-连接的对称负载 ---
                        g_a = dev_a.terminals.get("G")
                        g_b = dev_b.terminals.get("G")
                        if g_a and g_b and g_a != g_b:
                            if _check_cross_beam_symmetry(dev_a, dev_b):
                                self.add_tag(dev_a, AC.TAG_LOAD_C)
                                self.add_tag(dev_b, AC.TAG_LOAD_C)
                                _register_helper(members, AC.STR_LOAD_C, AC.STR_LOAD_C)
                                processed_devices.update([dev_a_name, dev_b_name])
                                continue

    # ---------------------------------------------登记低压电流镜中的对称镜像对---------------------------------------------------
    def _register_lv_mirror_pairs(self):
        """
        遍历所有电流束中的 *实际路径*，查找是否存在上层镜像管和下层镜像管在路径中连续出现的情况。
        如果存在，则将它们登记为 "低压镜像对"。（假设偏置电路中没有电流束）

        **要在识别低压电流镜后、分析电流束后调用**
        _detect_low_voltage_current_mirrors 之后 
        analyze_current_beams 之后
        """
        AC = self.AC

        processed_pairs = set()  # 避免同一对被重复登记

        # 遍历所有电流束
        for paths_list in self.circuit.current_beams.values():
            for path in paths_list:
                devices = path[::2] # [M1, M2, M3...]
                if len(devices) < 2: continue
                
                for i in range(len(devices) - 1):
                    name_a = devices[i]
                    name_b = devices[i+1]
                    
                    pair_key = frozenset([name_a, name_b])
                    if pair_key in processed_pairs: continue

                    dev_a = self.circuit.devices_dict.get(name_a)
                    dev_b = self.circuit.devices_dict.get(name_b)
                    if not dev_a or not dev_b: continue

                    # 2. 检查是否为 上/下 镜像对
                    is_u_a = AC.TAG_LV_UPPER_MIRROR in dev_a.tags
                    is_l_a = AC.TAG_LV_LOWER_MIRROR in dev_a.tags
                    is_u_b = AC.TAG_LV_UPPER_MIRROR in dev_b.tags
                    is_l_b = AC.TAG_LV_LOWER_MIRROR in dev_b.tags

                    is_match = (is_u_a and is_l_b) or (is_l_a and is_u_b)
                    
                    if is_match:
                        self.add_tag(dev_a, AC.TAG_LV_PAIR)
                        self.add_tag(dev_b, AC.TAG_LV_PAIR)
                        self.add_group(AC.STR_LV_MIRROR_PAIR, [name_a, name_b])
                        self.aggregate_substructure(AC.STR_LV_MIRROR_PAIR, [dev_a, dev_b])
                        processed_pairs.add(pair_key)

    # ---------------------------------------------登记低压电流镜 ---------------------------------------------------
    def _register_lv_mirrors(self):
        """
        这里完全就是走个形式，实际成员都是从 RelationGraph 中获取的。
        只要保证 RelationGraph 构建正确即可。
        
        **要在识别低压电流镜后调用**
        _detect_low_voltage_current_mirrors 之后
        """
        AC = self.AC

        # 1. 获取所有锚点 (下层参考管)
        lower_refs = self.get_names_by_tag(AC.TAG_LV_LOWER_REF)
        
            
        # 2. 从关系图中拉取成员
        # 注意：我们在 _mark_low_voltage_mirrors 中定义了这些关系键
        for l_ref_name in lower_refs:
        # 从 RelationGraph 提取成员
            u_ref_names = self.get_relations(l_ref_name, AC.REL_LV_LREF2UREF)
            u_bias_names = self.get_relations(l_ref_name, AC.REL_LV_LREF2UBIAS)
            tokens = self.get_relations(l_ref_name, AC.REL_LV_LREF2TOKEN)
            
            all_names = {l_ref_name} | set(u_ref_names) | set(u_bias_names) | set(tokens)
            members = []
            for name in all_names:
                d = self.circuit.devices_dict.get(name)
                if d: members.append(d)
            
            # 至少 4 个成员 (LRef, URef, 2 Mirrors)
            if len(members) >= 4:
                self.aggregate_substructure(AC.STR_LV_MIRROR, members)

    # -----------------------------------------------登记普通电流镜 --------------------------------------------------
    def _register_current_mirrors(self):
        """
        这里完全就是走个形式，实际成员都是从 RelationGraph 中获取的。
        只要保证 RelationGraph 构建正确即可。
        
        **要在识别低压电流镜后调用**
        _detect_low_voltage_current_mirrors之后
        """
        AC = self.AC
        # 1. 获取所有参考管
        refs = self.get_names_by_tag(AC.TAG_STD_MIRROR_REF)
        
        for ref_name in refs:
            mirrors = self.get_relations(ref_name, AC.REL_STD_REF2MIRROR)
            
            all_names = {ref_name} | set(mirrors) 
            members = []
            for name in all_names:
                d = self.circuit.devices_dict.get(name)
                if d: members.append(d)
                
            if len(members) >= 2:
                self.aggregate_substructure(AC.STR_STD_MIRROR, members)

    # ---------------------------------------缓存尾电流源--------------------------------------------
    def _get_tail_current(self):
        """
        识别电路中的尾电流源：
        1. 输入回路 (beam_2_differential): 长度为1的元素 -> input_tail
        2. 公共部分 (Overlap): 检测 beam_1 和 beam_2 的重合元素，提取共栅对 -> common_tail
        3. 输出回路 (beam_3_output): 剔除重合元素后，根据典型负载和低压镜像对标签提取 -> output_tail

        **要在分析电流束之后、识别典型负载与低压镜像对后调用**
        _register_beam_substructures 之后
        _register_lv_mirror_pairs 之后
        """
        AC = self.AC
        # 获取路径数据，若不存在则返回
        path1 = self.circuit.current_beam_paths.get("beam_2_differential")
        path2 = self.circuit.current_beam_paths.get("beam_3_output")

        if not path1:
            return
        # -----------------------------------------------------
        # 1. 处理输入回路尾电流源 (self.input_tail)
        # -----------------------------------------------------
        for element_set in path1:
            if len(element_set) == 1:
                # 提取唯一的管子名称
                # set无序，转list取第0个即可，不需要排序
                dev_name = list(element_set)[0]
                self.add_group(AC.STR_TAIL_INPUT, [dev_name])

        if not path2:
            return
        # -----------------------------------------------------
        # 2. 检测重合元素并处理公共尾电流源 (self.common_tail)
        # -----------------------------------------------------
        overlap_element = None

        # 检测重合 (Set 内容相等)
        # 默认重合元素只会存在一个，找到即停止
        for s1 in path1:
            for s2 in path2:
                if s1 == s2:
                    overlap_element = s1
                    break
            if overlap_element:
                break

        # 处理重合元素中的共栅对
        if overlap_element:
            overlap_devs = list(overlap_element)
            processed_mos = set()  # 用于记录已配对的管子，防止重复使用

            if len(overlap_devs) >= 2:
                for name_a, name_b in itertools.combinations(overlap_devs, 2):
                    if name_a in processed_mos or name_b in processed_mos:
                        continue

                    dev_a = self.circuit.devices_dict.get(name_a)
                    dev_b = self.circuit.devices_dict.get(name_b)

                    # 确保只处理 MOS 管
                    if not dev_a or not dev_b:
                        continue
                    if dev_a.type not in ["PMOS", "NMOS"] or dev_b.type not in ["PMOS", "NMOS"]:
                        continue

                    g_a = dev_a.terminals.get("G", "")
                    g_b = dev_b.terminals.get("G", "")

                    # 检查栅极是否连接在一起
                    if self._net_matches(g_a, {g_b}):
                        self.add_group(AC.STR_TAIL_COMMON, [name_a, name_b])
                        processed_mos.add(name_a)
                        processed_mos.add(name_b)

        # -----------------------------------------------------
        # 3. 处理输出回路尾电流源 (self.output_tail)
        # -----------------------------------------------------

        # 剔除重合元素 (如果存在)
        # 这里的 filtered_path2 是 List[Set[str]]
        if overlap_element:
            filtered_path2 = [s for s in path2 if s != overlap_element]
        else:
            filtered_path2 = list(path2)

        # 遍历剩下的元素
        n = len(filtered_path2)
        i = 0
        while i < n:
            current_set = filtered_path2[i]
            current_list = list(current_set)

            # 健壮性检查：虽然逻辑上剩下的一定是长度为2，但防止空集
            if not current_list:
                i += 1
                continue

            # 挑出第一个管子名称进行判断 (因为元素内管子等价)
            first_name = current_list[0]
            dev = self.circuit.devices_dict.get(first_name)

            if not dev:
                i += 1
                continue

            # 检查标签
            has_typ = AC.TAG_LOAD_TYP in dev.tags
            has_lv_pair = AC.TAG_LV_PAIR in dev.tags

            # 规则: 若不存在典型负载标签，直接跳过
            if not has_typ:
                i += 1
                continue

            # 存在典型负载标签
            if not has_lv_pair:
                # 情况 A: 不存在低压电流镜镜像对标签
                # 存入当前两个管子 [A, B]
                self.add_group(AC.STR_TAIL_OUTPUT, current_list)
                i += 1
            else:
                # 情况 B: 存在低压电流镜镜像对标签
                # 存入当前两个 + 下一个元素的两个 [A, B, C, D]
                # 基于逻辑保证：下一个元素一定存在
                if i + 1 < n:
                    next_list = list(filtered_path2[i + 1])
                    combined_list = current_list + next_list
                    self.add_group(AC.STR_TAIL_OUTPUT, combined_list)
                    # 跳过下一个元素，处理下下个
                    i += 2
                else:
                    # 异常情况防越界（理论不应到达）
                    i += 1

    #--------------------------------------------------输出对----------------------------------------------------
    def _get_output_pair(self):
        """
        识别输出对 (Output Pair)。
        定义：对于一个输出端对，如果这两个管子的栅极网络在第一个电流束 (beam_2_differential)
        的电流束网络集合中，则它们构成输出对。

        **要在登记电流束结构之后调用**
        _register_beam_substructures 之后
        """
        # 1. 获取第一个电流束的网络集合
        # 对应 "beam_net_sets中第一个键的值"
        AC = self.AC

        beam1_nets = self.circuit.beam_net_sets.get("beam_2_differential")

        if not beam1_nets:
            return

        # 为了确保匹配的健壮性，使用小写集合进行比较 (与 _net_matches 逻辑保持一致)
        beam1_nets_lower = {n.lower() for n in beam1_nets}

       # 2. 获取候选的 "输出端对" (从之前的步骤中注册的分组获取)
        candidate_pairs = self.device_groups.get(AC.STR_OUTPORT_PAIR, []) # List[List[str]]

        for pair in candidate_pairs:
            # pair 是 [name_a, name_b]
            if len(pair) < 2:
                continue

            name_a, name_b = pair[0], pair[1]
            dev_a = self.circuit.devices_dict.get(name_a)
            dev_b = self.circuit.devices_dict.get(name_b)
            if not dev_a or not dev_b:
                continue

            # 3. 获取它们的栅极名称
            g_net_a = dev_a.terminals.get("G")
            g_net_b = dev_b.terminals.get("G")
            if not g_net_a or not g_net_b:
                continue

            # 4. 检测是否是子集
            # 即：两个管子的栅极网络都在 beam1 的网络集合中
            if g_net_a.lower() in beam1_nets_lower and g_net_b.lower() in beam1_nets_lower:
                self.add_group(AC.STR_OUTPUT_PAIR, pair)
                self.add_tag(dev_a, AC.TAG_OUTPUT_POS) # 简化分配
                self.add_tag(dev_b, AC.TAG_OUTPUT_NEG)
                self.aggregate_substructure(AC.STR_OUTPUT_PAIR, [dev_a, dev_b])
                break

    # ------------------------------------------登记频率补偿和RC共模检测 ------------------------------------------------
    def _register_rc_structures(self):
        """
        将所有打上特定 Tag 的器件聚合为一个全局子结构，子结构内电容参数相等、电阻参数相等

        **要在标记输出端器件后调用**
        _mark_output_devices 之后
        """
        AC = self.AC

        # 1. 登记 频率补偿
        # [Refactor] 直接查询拥有 COMPENSATE 标签的所有器件
        # 频率补偿
        comp_members = self.get_devices_by_tag(AC.TAG_COMPENSATE)
        if comp_members:
            self.aggregate_substructure(AC.STR_FREQ_COMPENSATE, comp_members)

        # RC 共模检测
        rc_cm_members = self.get_devices_by_tag(AC.TAG_RC_CM_DETECT)
        if rc_cm_members:
            self.aggregate_substructure(AC.STR_RC_CM_DETECT, rc_cm_members)

    # -------------------------------------------登记对称电容-------------------------------------------
    def _register_sym_capacitors(self):
        """
        遍历所有未被分配的电容, 检查对称性。
        规则：电容信号端连接的MOS管处在至少一个同一个电流束中。

        **要在标记输出端器件后调用**
        _mark_outport_devices 之后
        """
        AC = self.AC

        # 1. 收集候选电容
        caps_to_check = []
        for d in self.circuit.devices_dict.values():
            if d.type == "Capacitor":
                # 排除已标记的电容
                if AC.TAG_COMPENSATE not in d.tags and AC.TAG_RC_CM_DETECT not in d.tags:
                    caps_to_check.append(d)

        if len(caps_to_check) < 2:
            return  # 没有足够的电容进行配对

        # 2. 遍历所有配对
        processed_caps = set()  # 避免重复登记
        for c1 in caps_to_check:
            if c1.name in processed_caps:
                continue

            for c2 in caps_to_check:
                if c1.name == c2.name or c2.name in processed_caps:
                    continue

                # 3. 获取 C1 和 C2 的网络及电源状态
                c1_net1 = c1.terminals.get("PLUS")
                c1_net2 = c1.terminals.get("MINUS")
                c2_net1 = c2.terminals.get("PLUS")
                c2_net2 = c2.terminals.get("MINUS")

                c1_pwr = (self._is_net_powerorgnd(c1_net1), self._is_net_powerorgnd(c1_net2))
                c2_pwr = (self._is_net_powerorgnd(c2_net1), self._is_net_powerorgnd(c2_net2))

                set_mos_1: Set[str] = set()
                set_mos_2: Set[str] = set()

                # 4. 应用 Case (I) / (II) / (III)

                # Case (I): 一端接电源，一端接信号 (对称)
                if c1_pwr.count(True) == 1 and c2_pwr.count(True) == 1:
                    c1_sig_net = c1_net1 if not c1_pwr[0] else c1_net2
                    c2_sig_net = c2_net1 if not c2_pwr[0] else c2_net2

                    set_mos_1 = self._get_mos_on_net(c1_sig_net, {c1.name})
                    set_mos_2 = self._get_mos_on_net(c2_sig_net, {c2.name})

                # Case (II): 两端均接信号 (对称)
                elif c1_pwr.count(True) == 0 and c2_pwr.count(True) == 0:
                    set_mos_1a = self._get_mos_on_net(c1_net1, {c1.name})
                    set_mos_1b = self._get_mos_on_net(c1_net2, {c1.name})
                    set_mos_2a = self._get_mos_on_net(c2_net1, {c2.name})
                    set_mos_2b = self._get_mos_on_net(c2_net2, {c2.name})

                    set_mos_1 = set_mos_1a.union(set_mos_1b)
                    set_mos_2 = set_mos_2a.union(set_mos_2b)

                # Case (III): 其他情况 (非对称，跳过)
                else:
                    continue

                # 5. 匹配检查与登记
                # 调用提取出的核心函数
                if self._check_mos_sets_in_one_beam(set_mos_1, set_mos_2):
                    self.add_tag(c1, AC.TAG_SYM_CAPACITOR)
                    self.add_tag(c2, AC.TAG_SYM_CAPACITOR)
                    
                    # [Refactor] 存入分组
                    self.add_group(AC.STR_SYM_CAPACITOR, [c1.name, c2.name])

                    # 登记
                    self.aggregate_substructure(AC.STR_SYM_CAPACITOR, [c1, c2])
                    # 标记为已处理
                    processed_caps.add(c1.name)
                    processed_caps.add(c2.name)
                    # 找到了 c1 的配对，跳出内层循环，开始找下一个 c1
                    break

    # -------------------------------------子结构实例登记函数-----------------------------------------
    def aggregate_substructure(self, struct_key: str, members: List['Device']):
        """
        [统一接口] 登记子结构实例。
        替换了原代码中分散的 aggregate_substructure 调用。
        
        Args:
            struct_key: AnalysisConfig.STR_XXX
            members: 器件对象列表
        """
        # 1. 获取定义
        sub_def = self.substructure_types.get(struct_key)
        if not sub_def:
            # 仅在开发阶段警告，生产环境可忽略或记录日志
            # print(f"[System] 未注册的子结构类型: {struct_key}")
            return

        # 2. 校验聚合规则 (Tag Check)
        member_roles = set().union(*[d.tags for d in members])
        if not sub_def.aggregation_rule(member_roles):
            # print(f"[System] {struct_key} 成员标签校验失败: {member_roles}")
            return

        # 3. 生成统一 ID
        sub_id = sub_def.generate_id(members)

        # 4. 生成对象化约束 (Constraint Objects)
        try:
            constraints = sub_def.constraint_generator(members)
        except Exception as e:
            traceback.print_exc()
            print(f"[Error] 约束生成异常 ({struct_key}): {e}")
            constraints = []

        # 5. 存储到 Circuit
        # 注意: CircuitSub.constraints 现在存储 List[Constraint] 对象
        self.circuit.substructures.append(self.CircuitSub(
            sub_id=sub_id,
            type=struct_key, 
            members=[d.name for d in members],
            constraints= constraints
        ))

        # 6. 反向索引
        for device in members:
            device.substructures.append(self.DeviceSub(sub_type=struct_key, sub_id=sub_id))


    #----------------------------------------------------约束生成------------------------------------------------------------
    def _generate_constraint_groups(self):
        """
        [重构版] 生成参数约束组。
        现在读取 Constraint 对象，不再解析字符串。
        """
        # 邻接表: { "M1_l": {"M2_l", "M3_l"}, ... }
        adj_list: DefaultDict[str, Set[str]] = defaultdict(set)

        # 1. 遍历所有已登记子结构的约束对象
        for instance in self.circuit.substructures:
            # instance.constraints 是 List[Constraint]
            for c in instance.constraints:
                # 仅处理 EQUAL 类型的约束用于生成连通分量
                # RATIO_W 类型 (fw 比例) 不参与强相等分组，由 r_raw 阶段独立处理
                if c.type == CircuitAnalyzer.ConstraintType.EQUAL:
                    # 构造参数全名: "M1_l"
                    param_a = f"{c.target_dev_name}_{c.target_param}"
                    param_b = f"{c.source_dev_name}_{c.source_param}"
                    
                    # 添加无向边
                    adj_list[param_a].add(param_b)
                    adj_list[param_b].add(param_a)

        # 2. 获取 *所有* 可能的参数 (作为节点全集)
        all_params_set: Set[str] = set()
        for device in self.circuit.devices_dict.values():
            for param_key in device.params.keys():
                all_params_set.add(f"{device.name}_{param_key}")

        # 3. 查找连通分量 (DFS)
        visited: Set[str] = set()
        all_components: List[List[str]] = []

        # 3a. 处理有约束的参数
        for param in adj_list:
            if param not in visited:
                component: List[str] = []
                stack: List[str] = [param]
                
                while stack:
                    node = stack.pop()
                    if node not in visited:
                        visited.add(node)
                        component.append(node)
                        # 邻居入栈
                        for neighbor in adj_list[node]:
                            if neighbor not in visited:
                                stack.append(neighbor)
                
                component.sort()
                all_components.append(component)

        # 3b. 处理孤立参数 (无约束)
        for param in all_params_set:
            if param not in visited:
                all_components.append([param])

        # 4. 存储结果
        self.constraint_groups = all_components

    # -----------------------------------------------------修改初始值 -----------------------------------------------------------
    def _parse_value_to_float(self, val_str: str) -> Optional[float]:
        """ 辅助函数：将 '10u', '805n', '2' 等字符串转为浮点数 """
        if val_str is None:
            return None
        val_str = val_str.lower().strip()
        multipliers = {'f': 1e-15, 'p': 1e-12, 'n': 1e-9, 'u': 1e-6, 'm': 1e-3,
                       'k': 1e3, 'meg': 1e6, 'g': 1e9}

        match = re.match(r"^(-?\d+\.?\d*|\.-?\d+)(.*)$", val_str)
        if not match:
            try:
                return float(val_str)  # 可能是纯数字
            except ValueError:
                print(f"警告：无法解析参数值 '{val_str}'")
                return None

        number_part, suffix = match.groups()
        value = float(number_part)

        if suffix in multipliers:
            value *= multipliers[suffix]

        return value

    def _format_float_to_string(self, value: float, key: str) -> str:
        """
        辅助函数：将浮点数转回工程字符串
        - 'm' 参数四舍五入到整数。
        - 'l'/'fw'/'segL'/'segW' 遵循 'u' 和 'n' 规则 (10nm 步进)。
        """

        # 规则 1: 'm' 参数必须为整数 (V5-3)
        if key == 'm':
            rounded_val = int(round(value))
            return str(rounded_val)

        if value == 0.0:
            return "0"

        # 规则 2: 圆整到最近的 10nm (1e-8)
        grid_step = 1e-8
        rounded_value = round(value / grid_step) * grid_step

        if rounded_value == 0.0:
            return "0"

        # 规则 3: 格式化 (优先 'u', 但 < 1u 时回退到 'n')
        if abs(rounded_value) >= 9.95e-7:  # 1.0u
            val_in_u = rounded_value * 1e6
            rounded_mantissa = round(val_in_u, 2)  # 'u' 保留两位小数
            return f"{rounded_mantissa}u"
        else:  # < 1.0u
            val_in_n = int(round(rounded_value * 1e9))  # 'n' 自动为 10 的倍数
            return f"{val_in_n}n"

    def _get_param_val(self, param_name: str, params_dict: Dict) -> Optional[str]:
        """ 辅助函数：从 device_params 字典中获取值 """
        try:
            dev, key = param_name.rsplit("_", 1)
            return params_dict[dev][key]
        except (KeyError, ValueError):
            print(f"警告：无法解析或找到参数 {param_name}")
            return None

    def _set_param_val(self, param_name: str, value: str, params_dict: Dict, log_prefix=""):
        """ 辅助函数：向 device_params 字典中设置值，并记录更改 """
        try:
            dev, key = param_name.rsplit("_", 1)
            if dev not in params_dict or key not in params_dict[dev]:
                print(f"{log_prefix}  [警告]: 尝试设置的参数 {param_name} 在 device_params 中不存在。")
                return

            old_val = params_dict[dev][key]
            if old_val != value:
                print(f"{log_prefix}  [校准]: {param_name} (原: {old_val}) -> {value}")
                params_dict[dev][key] = value
        except (KeyError, ValueError):
            print(f"警告：无法设置参数 {param_name}")

    def _is_copy_tube(self, target_dev: 'CircuitAnalyzer.Device', ref_dev: 'CircuitAnalyzer.Device') -> bool:
        """
        辅助函数：检查一个 'l' 参数是否属于"复制管"。
        普通电流镜：参考管是根参考管，所有镜像管都是复制管；参考管在偏置电路不是根参考管，所有非偏置镜像管是复制管；参考管在主电路，所有镜像管是复制管
        低压电流镜：下层参考管在主电路，所有镜像管是复制管；下层参考管在偏置电路，所有非偏置镜像管是复制管

        """
        AC = self.AC

        # 1. 参考管状态
        ref_is_root = AC.TAG_ROOT_REF in ref_dev.tags
        ref_in_beam = AC.TAG_IN_CURRENT_BEAM in ref_dev.tags
        
        # 2. 目标管状态
        target_in_beam = AC.TAG_IN_CURRENT_BEAM in target_dev.tags
        
        # 判定
        if ref_is_root or ref_in_beam:
            return True # 必须复制
        else:
            # Ref 是 Bias，看 Target
            if target_in_beam:
                return True # Bias -> Beam (提供电流)，需要复制
            else:
                return False # Bias -> Bias (传递电压/电流)，严格相等

    # ----------------------------------------------------- 预计算 r_raw -----------------------------------------------------------
    def _get_w_over_l(self, dev_name: str, params_dict: Dict) -> Optional[float]:
        """ 辅助函数：从指定的参数字典中计算 W/L """
        try:
            params = params_dict[dev_name]
            fw_str = params.get('fw')
            m_str = params.get('m')
            l_str = params.get('l')

            if fw_str is None or m_str is None or l_str is None:
                print(f"警告：(W/L) {dev_name} 缺少 fw/m/l 参数。")
                return None

            fw = self._parse_value_to_float(fw_str)
            m = float(m_str)  # m 可以是浮点数，但在格式化时会四舍五入
            l = self._parse_value_to_float(l_str)

            if l == 0.0 or l is None or fw is None:
                print(f"警告：(W/L) {dev_name} 参数解析失败或 l=0。")
                return None

            return (fw * m) / l
        except (KeyError, ValueError, TypeError) as e:
            print(f"警告：(W/L) 计算 {dev_name} 时出错: {e}")
            return None

    def _precompute_r_raw_map(self):
        """
        在任何校准发生前，遍历所有电流镜，计算并存储所有“复制管”
        相对于其参考管的 *原始* W/L 比例 (r_raw)。
        修正：LV 镜的上层和下层管必须使用各自的 W/L 参考。

        这里存在逻辑冗余
        """
        AC = self.AC

        print("\n" + "=" * 30 + " 预计算 r_raw 真值 " + "=" * 30)
        # 使用 self.device_params (原始CDF值)
        params_dict = self.device_params

        # --- 1. 普通电流镜 ---
        std_refs = self.get_names_by_tag(AC.TAG_STD_MIRROR_REF)
        for ref_name in std_refs:
            ref_dev = self.circuit.devices_dict.get(ref_name)
            if not ref_dev: continue

            # 获取 W/L
            ref_wl = self._get_w_over_l(ref_name, params_dict)
            if ref_wl is None: continue

            # 遍历镜像管
            mirrors = self.get_relations(ref_name, AC.REL_STD_REF2MIRROR)
            for m_name in mirrors:
                m_dev = self.circuit.devices_dict.get(m_name)
                if not m_dev: continue

                # 判定是否为复制管
                if self._is_copy_tube(m_dev, ref_dev):
                    m_wl = self._get_w_over_l(m_name, params_dict)
                    if m_wl is None: continue
                    
                    r_raw = m_wl / ref_wl
                    self.copy_tube_r_raw_map[m_name] = (ref_name, r_raw)
                    print(f"  [STD] CopyTube: {m_name} (Ref: {ref_name}), r_raw={r_raw:.4f}")

        # --- 2. 低压电流镜 ---
        lv_lower_refs = self.get_names_by_tag(AC.TAG_LV_LOWER_REF)
        for l_ref_name in lv_lower_refs:
            l_ref_dev = self.circuit.devices_dict.get(l_ref_name)
            if not l_ref_dev: continue
            
            # 获取 Lower Ref W/L
            l_ref_wl = self._get_w_over_l(l_ref_name, params_dict)
            
            # 获取 Upper Ref (通过关系)
            u_ref_names = self.get_relations(l_ref_name, AC.REL_LV_LREF2UREF)
            if not u_ref_names: continue
            u_ref_name = u_ref_names[0] # 理论上只有一个
            u_ref_wl = self._get_w_over_l(u_ref_name, params_dict)

            if l_ref_wl is None or u_ref_wl is None: continue

            # 遍历所有 Token (Upper Mirrors + Lower Mirrors)
            tokens = self.get_relations(l_ref_name, AC.REL_LV_LREF2TOKEN)
            for t_name in tokens:
                t_dev = self.circuit.devices_dict.get(t_name)
                if not t_dev: continue

                # 判定: 这里的参考对象是 Lower Ref 还是 Upper Ref?
                # _is_copy_tube 的逻辑主要是判断拓扑位置，用 Lower Ref 代表整个结构即可
                if self._is_copy_tube(t_dev, l_ref_dev):
                    t_wl = self._get_w_over_l(t_name, params_dict)
                    if t_wl is None: continue
                    
                    # 确定具体的 Reference W/L
                    target_ref_wl = None
                    target_ref_name = None
                    
                    if AC.TAG_LV_UPPER_MIRROR in t_dev.tags:
                        target_ref_wl = u_ref_wl
                        target_ref_name = u_ref_name
                    elif AC.TAG_LV_LOWER_MIRROR in t_dev.tags:
                        target_ref_wl = l_ref_wl
                        target_ref_name = l_ref_name
                    else:
                        # Fallback (不应发生)
                        target_ref_wl = l_ref_wl
                        target_ref_name = l_ref_name
                    
                    if target_ref_wl == 0: continue

                    r_raw = t_wl / target_ref_wl
                    # 注意：存储时 Ref Name 统一存 Lower Ref Name (作为 Group Key)
                    # 这样在 Phase 2 时可以统一处理
                    self.copy_tube_r_raw_map[t_name] = (l_ref_name, r_raw)
                    print(f"  [LV]  CopyTube: {t_name} (Ref: {target_ref_name}), r_raw={r_raw:.4f}")

        print("=" * 30 + " r_raw 预计算完成 " + "=" * 30)

    # ----------------------------------------------------- 两阶段校准 -----------------------------------------------------------
    def _calibrate_device_params(self):
        """
        基于两阶段校准：
        1. 阶段一：应用非电流镜约束（允许“污染”复制管），推迟电流镜约束。
        2. 阶段二：在最后，基于 r_raw 真值对复制管进行最终补偿。
        """
        # 0. 目标字典和约束组
        AC = self.AC

        new_device_params = copy.deepcopy(self.device_params)
        groups_to_process = self.constraint_groups

        TAG_PRIORITY_ORDER = [
            AC.TAG_ROOT_REF,
            AC.TAG_STD_MIRROR_REF,
            AC.TAG_LV_LOWER_REF,
            AC.TAG_CASCODE_MAIN
        ]

        # =================================================================
        # 阶段一：约束应用与条件推迟 (“污染”阶段)
        # =================================================================
        for group in groups_to_process:
            if not group:
                continue

            golden_ref_param = None
            golden_val_str = None

            # --- 1. 黄金标准搜索 ---
            for tag in TAG_PRIORITY_ORDER:
                # 这里直接break是因为之前通过图算法生成的约束组合已经把整个电路所有子结构都考虑了，即TAG_PRIORITY_ORDER内部4个标签无论顺序怎么变，结果应该是一样的，只是代码运行时间会有区别
                if golden_ref_param: break
                for param_name in group:
                    try:
                        dev_name = param_name.rsplit("_", 1)[0]
                        if tag in self.circuit.devices_dict[dev_name].tags:
                            golden_ref_param = param_name
                            break
                    except KeyError:
                        continue

            # --- 2. 检查黄金参考是否为 CM 参考管 ---
            is_ref_mirror_ref = False
            if golden_ref_param:
                try:
                    dev_name, key = golden_ref_param.rsplit("_", 1)
                    dev_tags = self.circuit.devices_dict[dev_name].tags
                    if (AC.TAG_STD_MIRROR_REF in dev_tags or
                            AC.TAG_LV_LOWER_REF in dev_tags):
                        is_ref_mirror_ref = True
                except (KeyError, ValueError):
                    pass  # dev_name 解析失败

            # --- 3. 获取黄金值  ---
            if golden_ref_param:
                golden_val_str = self._get_param_val(golden_ref_param, new_device_params)
            else:
                # --- 4. 平票平均值 (如果没找到层级标准) ---
                param_key = group[0].rsplit("_", 1)[-1]
                values_float = []
                for param_name in group:
                    val_str = self._get_param_val(param_name, new_device_params)
                    if val_str:
                        val_float = self._parse_value_to_float(val_str)
                        if val_float is not None:
                            values_float.append(val_float)

                if not values_float:
                    print("    [警告]: 组内无可解析的值，跳过。")
                    continue

                avg_float = sum(values_float) / len(values_float)
                golden_val_str = self._format_float_to_string(avg_float, param_key)

            if golden_val_str is None:
                print(f"    [警告]: 无法确定 {group[0]} 的黄金标准值。")
                continue

            # --- 5. 应用约束  ---
            for target_param in group:
                # 情况 A: 黄金标准是CM参考管
                if is_ref_mirror_ref:
                    target_dev_name, _ = target_param.rsplit("_", 1)
                    # 检查目标是否为“复制管”
                    if target_dev_name in self.copy_tube_r_raw_map:
                        continue    # 是复制管 -> 推迟操作
                    else:
                        # 不是复制管 -> 正常应用
                        self._set_param_val(target_param, golden_val_str, new_device_params, log_prefix="  ")

                # 情况 B: 黄金标准非CM参考管 (或来自平均值)
                else:
                    # 正常应用 -> 允许“污染”
                    self._set_param_val(target_param, golden_val_str, new_device_params, log_prefix="  ")

        # =================================================================
        # 阶段二：最终补偿 (“拨乱反正”阶段)
        # =================================================================
        # 1. 按参考管重组复制管
        ref_to_copy_tubes_map: DefaultDict[str, List[str]] = defaultdict(list)
        for copy_dev, (ref_dev, r_raw) in self.copy_tube_r_raw_map.items():
            ref_to_copy_tubes_map[ref_dev].append(copy_dev)

        # 2. 遍历每个电流镜组
        for ref_dev_name, copy_dev_list in ref_to_copy_tubes_map.items():
            # 3. A/B 类划分 (基于阶段一 "污染" 后的参数)
            param_groups: DefaultDict[tuple, List[str]] = defaultdict(list)
            for dev_name in copy_dev_list:
                try:
                    params = new_device_params[dev_name]
                    fw = params['fw']
                    m = params['m']
                    l = params['l']
                    param_groups[(fw, m, l)].append(dev_name)
                except KeyError:
                    continue

            # 4. 处理 A 类 (对称) 和 B 类 (独立)
            for (fw_now, m_now, l_now_unused), dev_group in param_groups.items():
                group_type = "A类 (对称)" if len(dev_group) > 1 else "B类 (独立)"

                try:
                    # 5. 计算 r_raw_target
                    r_raw_list = [self.copy_tube_r_raw_map[dev_name][1] for dev_name in dev_group]
                    r_raw_target = sum(r_raw_list) / len(r_raw_list)

                    # 6. 获取参考管 *当前* (阶段一后) 的 W 和 L
                    ref_fw_str = new_device_params[ref_dev_name]['fw']
                    ref_m_str = new_device_params[ref_dev_name]['m']
                    ref_l_str = new_device_params[ref_dev_name]['l']

                    W_ref_now_float = self._parse_value_to_float(ref_fw_str) * float(ref_m_str)
                    L_new_str = ref_l_str  # 目标 L = 参考管的 L

                    # 7. 获取复制管 *当前* (阶段一后) 的 W
                    W_copy_now_float = self._parse_value_to_float(fw_now) * float(m_now)

                    if W_ref_now_float == 0.0:
                        print(f"    [警告]: 参考管 {ref_dev_name} 当前 W=0, 无法补偿。")
                        continue

                    # 8. 计算 r_now (W 的比值)
                    r_now_W_ratio = W_copy_now_float / W_ref_now_float

                    fw_new_str = fw_now
                    m_new_str = m_now

                    # 9. 检查是否需要补偿 (比较 W比值 和 目标W/L比值)
                    # 数学上, 要让W_target/W_ref = r_raw_target (因为 L_new=L_ref)
                    if abs(r_now_W_ratio - r_raw_target) > 1e-9:
                        print(f"    [补偿需求]: r_now_W ({r_now_W_ratio:.4f}) != r_raw_target ({r_raw_target:.4f})")

                        # 简单计算可知：W_target = W_ref_now * r_raw_target
                        W_target = W_ref_now_float * r_raw_target

                        m_target = float(m_now)
                        fw_target = W_target / m_target

                        # 10. 应用 DRC 感知的 fw/m 补偿逻辑
                        if fw_target <= 50e-6 and fw_target > 0:  # Case 3
                            fw_new_str = self._format_float_to_string(fw_target, 'fw')
                            m_new_str = m_now

                        else:  # Case 2
                            m_target_float = math.ceil(fw_target / 50e-6)
                            if m_target_float > 300:  # Case 1
                                print(f"    [补偿]: (Case 1) 失败. {dev_group[0]} fw/m 均超限。跳过此组。")
                                L_new_str = ref_l_str
                                fw_new_str = fw_now
                                m_new_str = m_now
                            else:
                                m_new_int = int(m_target_float)
                                fw_final = W_target / m_new_int
                                fw_new_str = self._format_float_to_string(fw_final, 'fw')
                                m_new_str = str(m_new_int)
                    else:
                        print(f"    [无需补偿]: r_now_W ≈ r_raw_target.")

                    # 11. 应用最终值 (fw, m, l) 到组内所有管子
                    for dev_name in dev_group:
                        self._set_param_val(f"{dev_name}_l", L_new_str, new_device_params, log_prefix="    ")
                        self._set_param_val(f"{dev_name}_fw", fw_new_str, new_device_params, log_prefix="    ")
                        self._set_param_val(f"{dev_name}_m", m_new_str, new_device_params, log_prefix="    ")

                except Exception as e:
                    print(f"    [严重错误]: 补偿组 {dev_group} 失败: {e}")
                    traceback.print_exc()

        self.calibrate_params = new_device_params

# ------------------------------
# 使用示例
# ------------------------------
if __name__ == "__main__":
    # 定义电路和缓存文件
    print(f"测试开始")
    