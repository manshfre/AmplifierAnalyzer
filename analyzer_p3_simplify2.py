from __future__ import annotations
import os
import copy
import traceback
import itertools
import re
import math
import logging
import json
import hashlib
from datetime import datetime, timezone
from dataclasses import dataclass, field
from typing import Dict, List, Callable, Set, Optional, DefaultDict, Tuple, Any, Union
from collections import defaultdict
from enum import Enum, auto

# ------------------------------
# 核心电路分析器
# ------------------------------
# 假设偏置电路没有电流束
# 假设偏置电路不放大电流
# 低压电流镜未考虑电阻
# 电流源路径的定义问题
# 未考虑电阻除频率补偿、共模检测外的子结构
# 未考虑电容除频率补偿、共模检测、滤波外的子结构
# RC相关频率补偿、共模检测、滤波基于预定义规则
# 默认级联管子与低压电流镜处在对称支路上(同时默认对称支路的管子参数一定相等)
# 等等
# ------------------------------
# Logging & Report (P1)
# ------------------------------
logger = logging.getLogger(__name__)

# ------------------------------
# Deterministic report timestamps
# ------------------------------
# 说明：默认使用确定性时间戳以保证“相同输入=>相同输出”。
# 如确需真实时间戳，可设置环境变量 ANALYZER_REALTIME_REPORT=1。
_DETERMINISTIC_TS_ISO = "2025-11-11T00:00:00+00:00"

def _report_now_iso() -> str:
    flag = (os.getenv("ANALYZER_REALTIME_REPORT", "0") or "0").strip().lower()
    if flag in ("1", "true", "yes", "y", "on"):
        return datetime.now(timezone.utc).isoformat()
    return _DETERMINISTIC_TS_ISO

@dataclass
class AnalysisReport:
    """结构化分析报告（用于替代 print，并支持软著材料固化与测试复现）"""
    created_at_utc: str = field(default_factory=_report_now_iso)
    events: List[Dict[str, Any]] = field(default_factory=list)
    calibrations: List[Dict[str, Any]] = field(default_factory=list)
    stats: Dict[str, Any] = field(default_factory=dict)

    def add_event(self, level: str, message: str, **context: Any) -> None:
        self.events.append({
            "ts_utc": _report_now_iso(),
            "level": level,
            "message": message,
            "context": context or {}
        })

    def add_calibration(self, param_name: str, old: str, new: str, **context: Any) -> None:
        self.calibrations.append({
            "ts_utc": _report_now_iso(),
            "param": param_name,
            "old": old,
            "new": new,
            "context": context or {}
        })

@dataclass(frozen=True)
class CalibrationConfig:
    """参数校准与格式化的可配置常量（替代魔数，支持审计与复现）"""
    # 格式化规则
    grid_step_m: float = 1e-8              # 10nm 步进
    micro_threshold_m: float = 9.95e-7     # >= 约 1.0u 则用 'u'
    micro_decimals: int = 2               # 'u' 小数位数
    ratio_tolerance: float = 1e-9         # 比值比较容差

    # DRC 感知补偿阈值（复制管补偿逻辑）
    fw_case3_max_m: float = 50e-6         # Case 3 上限
    m_case1_max: int = 300               # Case 1 上限

    # 维度约束（解析时）
    require_positive_length: bool = True
    require_positive_multiplier: bool = True

@dataclass(frozen=True)
class AnalysisRule:
    """声明式分析规则（用于将 pipeline 从硬编码序列重构为可声明、可审计的规则列表）"""
    name: str
    func_name: str
    requires: Tuple[str, ...] = ()  # 需要存在的属性路径（如 'circuit.current_paths'）
    optional: bool = False          # True 时前置条件不满足则跳过；False 则记录为错误并继续
    description: str = ""

class CircuitAnalyzer:
    """
    基于规则获取子结构的电路分析器 (CircuitAnalyzer)
    调用后可对电路的子结构进行识别、对参数进行精简、对初始解进行修改
    AnalysisConfig定义分析器工作逻辑所使用的字符串；
    APPConfig定义分析器的工作对象，CircuitPorts定义目标电路的端口名称集合，二者共同定义分析器的工作域
    Device是该分析器识别到的器件、DeviceSub是器件所属子结构实例的引用
    Circuit是该分析器识别到的电路、CircuitSub是在Circuit中识别出的子结构实例
    子结构要先注册到SubStructureType中，才能被识别并登记到CircuitSub中与DeviceSub中
    子结构包含约束函数，所有约束函数在ConstraintLibrary中列出，约束格式以Constraint对象给出，约束关系以ConstraintType给出
    """
    # ------------------------------
    # 1. 内部类定义
    # ------------------------------
    class AnalysisConfig:
        """
        TAG键代表分析器所存储的标签，它构成子结构的聚类规则，子结构的识别过程就是获取所配置的TAG键的过程；同时，在子结构的约束函数中有所使用（按标签找所需器件、子结构注册规则、分析器的工作目标）
        REL键代表存在主从关系的子结构的“主从关系”，它用于存储存在“关系”的器件，如主级联和从级联，作用是辅助子结构识别与参数修改（按关系找到所需的器件）。
        STR键用于不存在主从关系的子结构中所含器件的存储，如差分输入对。同时，用于构成子结构的注册名称和聚类id（按组合找到所需的器件、子结构注册名称、约束函数名称、聚类名称的规范化）
        简单的说，TAG键是工作目标，自己设定，自己获取，TAG键要全，以构成一个完整的子结构。REL、STR键用于方便TAG键的获取，同时让子结构的注册、识别、聚类过程规范化。

        注意：
        要对子结构的注册（注册名称、聚类规则、约束函数）、子结构识别过程与对应器件存储（按三类型键索引）、聚类名称（子结构id）进行变动（修改现有或增添），需修改此配置
        对应一个子结构，TAG与STR键是必须的，TAG键需要完备
        
        概述：
        1. 提供所有架构层面的常量（Tags, Relations, Structures, Ports）
        2. 提供各种键的中文描述映射
        3. 支持运行时动态添加/删除常量（用于扩展分析器能力）
        4. 约束函数名称-子结构注册名称-特殊器件索引名称-子结构聚类名称规范化
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
        # 2. 静态中文描述映射 (Static Chinese Map)
        # 键必须是变量名 (Variable Name)，如 "STR_DIFF_PAIR"
        # =========================================================================
        _STATIC_CHINESE_MAP = {
            # --- Structure ---
            "STR_DIFF_PAIR":       "差分输入对",
            "STR_CASCODE":         "级联结构",
            "STR_STD_MIRROR":      "普通电流镜",
            "STR_LV_MIRROR":       "低压电流镜",
            "STR_LV_MIRROR_PAIR":  "低压镜像对",
            "STR_LOAD_TYPICAL":    "典型负载",
            "STR_LOAD_A":          "A型负载",
            "STR_LOAD_B":          "B型负载",
            "STR_LOAD_C":          "C型负载",
            "STR_OUTPORT_PAIR":    "输出端对",
            "STR_OUTPUT_PAIR":     "逻辑输出对",
            "STR_CM_DETECT_A":     "2管共模检测",
            "STR_CM_DETECT_B":     "4管共模检测",
            "STR_RC_CM_DETECT":    "RC共模检测",
            "STR_FREQ_COMPENSATE": "频率补偿",
            "STR_SYM_CAPACITOR":   "对称电容",
            "STR_TAIL_INPUT":      "输入尾电流源",
            "STR_TAIL_COMMON":     "公共尾电流源",
            "STR_TAIL_OUTPUT":     "输出尾电流源",

            # --- Relation ---
            "REL_CASCODE_M2S":     "级联主从关系",
            "REL_STD_REF2MIRROR":  "普通镜像关系",
            "REL_STD_REF2BIAS":    "普通偏置关系",
            "REL_STD_ROOT2BIAS":   "根偏置锁定关系",
            "REL_LV_LREF2UREF":    "低压参考垂直关系",
            "REL_LV_LREF2UBIAS":   "低压上偏置关系",
            "REL_LV_LREF2TOKEN":   "低压镜像投射关系",

            # --- Tag ---
            "TAG_DIODE_MOS":            "二极管连接MOS",
            "TAG_IN_CURRENT_BEAM":      "处在电流束",
            "TAG_CASCODE_MAIN":         "级联主管",
            "TAG_CASCODE_SLAVE":        "级联从管",
            "TAG_DIFF_POS":             "差分输入正端",
            "TAG_DIFF_NEG":             "差分输入负端",
            "TAG_OUTPORT_POS":          "物理输出正端",
            "TAG_OUTPORT_NEG":          "物理输出负端",
            "TAG_OUTPUT_POS":           "逻辑输出正端",
            "TAG_OUTPUT_NEG":           "逻辑输出负端",
            "TAG_STD_MIRROR_REF":       "普通镜参考管",
            "TAG_STD_MIRROR_MIRROR":    "普通镜镜像管",
            "TAG_STD_MIRROR_BIAS":      "普通镜偏置管",
            "TAG_ROOT_REF":             "根参考管",
            "TAG_LV_UPPER_REF":         "低压镜上参考",
            "TAG_LV_LOWER_REF":         "低压镜下参考",
            "TAG_LV_UPPER_BIAS":        "低压镜上偏置",
            "TAG_LV_UPPER_MIRROR":      "低压镜上镜像",
            "TAG_LV_LOWER_MIRROR":      "低压镜下镜像",
            "TAG_LV_BIAS_MIRROR":       "低压镜偏置镜像",
            "TAG_LV_PAIR":              "低压对称对成员",
            "TAG_LOAD_TYP":             "典型负载管",
            "TAG_LOAD_A_DIO":           "A型负载二极管",
            "TAG_LOAD_A_TYP":           "A型负载镜像管",
            "TAG_LOAD_B":               "B型负载管",
            "TAG_LOAD_C":               "C型负载管",
            "TAG_CM_OUTER":             "共模检测外侧管",
            "TAG_CM_INNER":             "共模检测内侧管",
            "TAG_CM_2MOS":              "2管共模成员",
            "TAG_CM_4MOS":              "4管共模成员",
            "TAG_COMPENSATE":           "频率补偿元件",
            "TAG_RC_CM_DETECT":         "RC共模元件",
            "TAG_SYM_CAPACITOR":        "对称电容元件",
            
            # --- Port ---
            "PORT_POWER_POS":      "电源正",
            "PORT_POWER_NEG":      "电源负/地",
            "PORT_INPUT_POS":      "信号输入正",
            "PORT_INPUT_NEG":      "信号输入负",
            "PORT_OUTPUT_POS":     "信号输出正",
            "PORT_OUTPUT_NEG":     "信号输出负",
            "PORT_COMMON_MODE":    "共模电平端口",
            "PORT_CURRENT_SOURCE": "理想电流源端口"
        }

        # =========================================================================
        # 3. 实例初始化与管理 (Instance Methods)
        # =========================================================================

        def __init__(self):
            # 记录运行时动态添加的 Keys (存储变量名)
            self._dynamic_keys = set()

            # 实例级中文映射字典：Key = 变量名 (如 "STR_DIFF_PAIR")
            # 直接复制静态字典作为初始状态
            self._chinese_map = self._STATIC_CHINESE_MAP.copy()

        # =========================================================================
        # 3. 管理方法 (Management Methods) 
        # =========================================================================

        def get_chinese_name(self, query: str) -> str:
            """
            获取常量的中文描述。
            """
            # 情况1: 直接查询键名
            if query in self._chinese_map:
                return self._chinese_map[query]

            return query

        def list_keys(self, prefix: str = "") -> Dict[str, str]:
            """列出所有常量 (合并静态定义与动态扩展)"""
            result = {}
            # 扫描所有大写属性 (包括静态类属性和实例属性)
            for name in dir(self):
                if name.startswith("_") or not name.isupper():
                    continue
                if prefix and not name.startswith(prefix):
                    continue
                
                val = getattr(self, name)
                if isinstance(val, str):
                    desc = self.get_chinese_name(name)
                    result[name] = f"{val} ({desc})"
            return result

        def add_key(self, attr_name: str, value: str, description: str = ""):
            """
            [动态扩展] 在运行时注册新的常量 (仅作用于当前实例)。
            """
            if hasattr(self, attr_name) or hasattr(self.__class__, attr_name):
                logger.warning(f"[AnalysisConfig] 警告: 覆盖已有常量 {attr_name}")
            else:
                self._dynamic_keys.add(attr_name)
                
            setattr(self, attr_name, value)
            if description:
                self._chinese_map[attr_name] = description
                
            logger.info(f"[AnalysisConfig] 已注册(实例级): {attr_name} = '{value}' ({description})")

        def remove_key(self, attr_name: str):
            """[动态扩展] 删除常量 (仅限实例属性)"""
            if not hasattr(self, attr_name):
                return
            
            # 仅允许删除实例属性，防止破坏类静态定义
            if attr_name in self.__dict__:
                delattr(self, attr_name)
                self._chinese_map.pop(attr_name, None)
                logger.info(f"[AnalysisConfig] 已移除: {attr_name}")
            else:
                logger.warning(f"[AnalysisConfig] 无法移除静态常量 {attr_name}")

        def get_all_structure_keys(self) -> set[str]:
            """获取所有结构 Key (STR_)"""
            return self._get_keys_by_prefix("STR_")
        
        def get_all_relation_keys(self) -> set[str]:
            """获取所有关系 Key (REL_)"""
            return self._get_keys_by_prefix("REL_")
        
        def get_all_tag_keys(self) -> set[str]:
            """获取所有标签 Key (TAG_)"""
            return self._get_keys_by_prefix("TAG_")
        
        def _get_keys_by_prefix(self, prefix: str) -> set[str]:
            """辅助函数：按前缀获取键"""
            keys = {k for k, v in self.__class__.__dict__.items() if k.startswith(prefix) and isinstance(v, str)}
            for k in self._dynamic_keys:
                if k.startswith(prefix):
                    keys.add(k)
            return keys

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

        # ==================== 2. 实例初始化 (Instance Isolation) ====================
        def __init__(self):
            # 将类属性(默认值) Shadow 为实例属性(当前值)
            # 使用 .copy() 确保修改互不影响
            self.POWER_POSITIVE = self.POWER_POSITIVE.copy()
            self.POWER_NEGATIVE = self.POWER_NEGATIVE.copy()
            self.INPUT_POSITIVE = self.INPUT_POSITIVE.copy()
            self.INPUT_NEGATIVE = self.INPUT_NEGATIVE.copy()
            self.OUTPORT_POSITIVE = self.OUTPORT_POSITIVE.copy()
            self.OUTPORT_NEGATIVE = self.OUTPORT_NEGATIVE.copy()
            self.COMMON_SIGN = self.COMMON_SIGN.copy()
            self.CURRENT_SOURCE = self.CURRENT_SOURCE.copy()

        # ==================== 3. 查询与操作接口 (Instance Methods) ====================

        def list_ports(self) -> Dict[str, Set[str]]:
            """
            查看当前实例的所有端口定义
            仅返回大写且为集合类型的实例属性
            """
            return {
                k: v.copy() 
                for k, v in self.__dict__.items() 
                if k.isupper() and isinstance(v, set)
            }

        def get_port(self, name: str) -> Optional[Set[str]]:
            """获取指定端口名称对应的集合"""
            return getattr(self, name, None)

        def add_port(self, name: str, value_set: Set[str]) -> None:
            """
            [动态] 添加新的端口常量 (仅当前实例生效)
            """
            # 校验命名规范
            if not name.isupper() or not name.replace("_", "").isalnum():
                raise ValueError("端口名称必须为大写字母+下划线格式（如 POWER_CUSTOM）")
            
            # 校验数据类型
            if not isinstance(value_set, set):
                raise TypeError("端口值必须是 set 类型")
            
            setattr(self, name, value_set.copy())
            logger.info(f"[CircuitPorts] Added/Updated port: {name}")

        def remove_port(self, name: str) -> None:
            """
            [动态] 删除指定的端口常量 (仅当前实例生效)
            """
            if hasattr(self, name):
                delattr(self, name)
                logger.warning(f"[CircuitPorts] Removed port: {name}")
            else:
                raise AttributeError(f"端口常量 '{name}' 不存在")

        def add_to_port(self, name: str, element: str) -> None:
            """
            [动态] 向现有端口集合中添加单个元素
            """
            current = getattr(self, name, None)
            if current is None:
                raise AttributeError(f"端口常量 '{name}' 不存在")
            
            if not isinstance(current, set):
                raise TypeError(f"{name} 不是集合类型，无法添加元素")
            
            current.add(element)

        def remove_from_port(self, name: str, element: str) -> None:
            """
            [动态] 从端口集合中删除指定元素
            """
            current = getattr(self, name, None)
            if current is None:
                raise AttributeError(f"端口常量 '{name}' 不存在")
            
            if not isinstance(current, set):
                raise TypeError(f"{name} 不是集合类型，无法删除元素")
            
            current.discard(element)
            logger.info(f"[CircuitPorts] port{name} 删除{element}")

        def reset_to_defaults(self) -> None:
            """
            重置当前实例的所有端口为类定义的默认值
            """
            # 重新执行初始化逻辑，覆盖当前的实例属性
            self.__init__()
            logger.info("[CircuitPorts] Reset to defaults")

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
        def __init__(self):
            # 核心存储 (实例属性)
            self.ALIAS_CONFIG = {
                "NMOS": "NMOS", "PMOS": "PMOS",
                "CAPACITOR": "Capacitor", "RESISTOR": "Resistor"
            }
            self.PORT_CONFIG = {
                "NMOS": {"G", "D", "S", "B"},
                "PMOS": {"G", "D", "S", "B"},
                "CAPACITOR": {"PLUS", "MINUS"},
                "RESISTOR": {"PLUS", "MINUS"}
            }
            self.PARAM_CONFIG = {
                "NMOS": {"m", "fw", "l"},
                "PMOS": {"m", "fw", "l"},
                "CAPACITOR": {"l"},
                "RESISTOR": {"segW", "segL"}
            }

        # ==================== 管理方法 ====================
        def add_device_type(self, key: str, default_alias: str) -> None:
            """[新增] 新增器件类型标识符"""
            if key in self.ALIAS_CONFIG:
                raise ValueError(f"禁止修改已有器件类型 '{key}'")
            self.ALIAS_CONFIG[key] = default_alias
            logger.info(f"[APPConfig] 新增器件类型: {key}")

        def add_port_config(self, key: str, ports: Set[str]) -> None:
            """[新增] 新增端口定义"""
            if key in self.PORT_CONFIG:
                raise ValueError(f"禁止修改已有端口定义 '{key}'")
            self.PORT_CONFIG[key] = ports.copy()
            logger.info(f"[APPConfig]新增器件端口：{key}")

        def remove_entry_strictly(self, key: str) -> None:
            """[删除] 删减 DEVICE/PORT 条目 (高风险)"""
            if key in self.ALIAS_CONFIG: del self.ALIAS_CONFIG[key]
            if key in self.PORT_CONFIG: del self.PORT_CONFIG[key]
            logger.warning(f"[APPConfig] Removed entry: {key}")

        def update_param_config(self, key: str, params: Set[str]) -> None:
            """[增/删/改] 配置参数集合"""
            self.PARAM_CONFIG[key] = params.copy()
            logger.warning(f"[APPConfig]变动{key}器件参数")

        # ==================== 查询接口 ====================
        def get_device_alias(self, key: str) -> str:
            if key not in self.ALIAS_CONFIG:
                raise KeyError(f"未知类型标识符 '{key}'")
            return self.ALIAS_CONFIG[key]
        
        def get_identifier_by_type(self, device_type: str) -> str:
            for key, type_name in self.ALIAS_CONFIG.items():
                if device_type == type_name:
                    return key
            raise ValueError(f"未知器件类型字符串 '{device_type}'")

        def get_legal_ports(self, key: str) -> Set[str]:
            if key not in self.PORT_CONFIG:
                raise KeyError(f"未配置端口 '{key}'")
            return self.PORT_CONFIG[key].copy()
        
        def get_legal_params(self, key: str) -> Set[str]:
            if key not in self.PARAM_CONFIG:
                raise KeyError(f"未配置参数 '{key}'")
            return self.PARAM_CONFIG[key].copy()
            
        def reset_to_defaults(self) -> None:
            self.__init__()
            logger.info("[APPConfig] Reset to defaults")

        def get_config_summary(self) -> Dict[str, Dict]:
            return {
                key: {
                    "alias": self.ALIAS_CONFIG.get(key),
                    "ports": self.PORT_CONFIG.get(key, set()).copy(),
                    "params": self.PARAM_CONFIG.get(key, set()).copy()
                }
                for key in self.ALIAS_CONFIG.keys()
            }

    @dataclass
    class DeviceSub:
        """存储每个Device所属子结构实例索引"""
        sub_type: str
        sub_id: str

    @dataclass(eq=False)
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
        EQUAL = auto()  # 强相等 (l=l, fw=fw)
        # 预留：可扩展其他约束类型（如比例/范围等）

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
        type: "CircuitAnalyzer.ConstraintType" = field(
        default_factory=lambda: CircuitAnalyzer.ConstraintType.EQUAL)
        
        def __repr__(self):
            op = "=="
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
            constraint_generator: Callable[[List[CircuitAnalyzer.Device], CircuitAnalyzer.AnalysisConfig], List[CircuitAnalyzer.Constraint]] # 约束生成逻辑
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
        def rule_pair_strict(members: List['CircuitAnalyzer.Device'], config: 'CircuitAnalyzer.AnalysisConfig') -> List['CircuitAnalyzer.Constraint']:
            """
            [严格配对] 对应: 差分对, 输出对, 共模检测A, C型负载, 典型负载(pair部分)
            原始逻辑: 成员间 fw/l/m 完全相等。
            """
            AC = config
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
        def rule_cascode(members: List['CircuitAnalyzer.Device'], config: 'CircuitAnalyzer.AnalysisConfig') -> List['CircuitAnalyzer.Constraint']:
            """
            [级联]
            原始逻辑: 找到 Main，所有 Slave 的 l/fw/m 必须与 Main 相同。
            """
            AC = config
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
        def rule_std_mirror(members: List['CircuitAnalyzer.Device'], config: 'CircuitAnalyzer.AnalysisConfig') -> List['CircuitAnalyzer.Constraint']:
            """
            [普通电流镜]
            原始逻辑复刻:
            - 所有镜像管: l 必须约束 (m.l = ref.l)。
            - 偏置镜像管 (BIAS):
                - 若 Ref 是 ROOT_REF: 偏置管之间 fw/m 互等 (独立于 Ref)。
                - 若 Ref 非 ROOT_REF: 偏置管 fw/m = Ref.fw/m。
            - 普通镜像管: **不生成** fw/m 约束 (原代码未对非偏置管生成 fw/m 约束字符串)。
            """
            AC = config
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
        def rule_lv_mirror(members: List['CircuitAnalyzer.Device'], config: 'CircuitAnalyzer.AnalysisConfig') -> List['CircuitAnalyzer.Constraint']:
            """
            [低压电流镜]
            原始逻辑复刻:
            1. 上层参考管 (Upper Ref) 与 下层参考管 (Lower Ref): fw/l/m 全等。
            2. 镜像管 (无论是 Upper 还是 Lower):
            - l: 始终等于 Lower Ref.l。
            - 若为偏置镜像管 (BIAS): fw/m 等于 Lower Ref.fw/m。
            - 若为普通镜像管: **不生成** fw/m 约束。
            """
            AC = config
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
        def rule_load_typical(members: List['CircuitAnalyzer.Device'], config: 'CircuitAnalyzer.AnalysisConfig') -> List['CircuitAnalyzer.Constraint']:
            """
            [典型负载] / [A型/B型负载] / [4管共模检测]
            原始逻辑: 最后一个器件作为参考，其他器件向其看齐 (fw/l/m 全等)。
            """
            AC = config
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
        def rule_rc_group(members: List['CircuitAnalyzer.Device'], config: 'CircuitAnalyzer.AnalysisConfig') -> List['CircuitAnalyzer.Constraint']:
            """
            [RC组] 适用于: 频率补偿, RC共模检测, 对称电容
            原始逻辑:
            - 电阻: segW, segL 相等 (如果存在)。
            - 电容: l 相等 (如果存在)。
            """
            AC = config
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
        AC = self.ac
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
    def __init__(self, calibration_config: Optional[CalibrationConfig] = None, report: Optional[AnalysisReport] = None, logger_: Optional[logging.Logger] = None,
                 app_config: Optional[APPConfig] = None,
                 circuit_ports: Optional[CircuitPorts] = None):
        """
        CircuitAnalyzer 初始化
        遵循原则：
        1. 必须使用 Graph-Driven Storage (tag_index, relation_graph, device_groups)。
        2. 禁止初始化特定业务逻辑的缓存列表 (如 diff_pair_positive, cascode_cache 等)。
        3. 所有子结构类型注册必须通过 registry 完成。
        """
        # [P1] 日志与报告（替代 print，支持审计/复现）
        self.logger: logging.Logger = logger_ or logging.getLogger(f"{__name__}.CircuitAnalyzer")
        self.report: AnalysisReport = report or AnalysisReport()
        self.calibration_config: CalibrationConfig = calibration_config or CalibrationConfig()

        # [Audit] pipeline 可重入：基线报告快照（输入阶段产生的事件/统计）
        self._baseline_report: Optional[Dict[str, Any]] = None

        # 1. 基础拓扑容器
        self.ac = self.AnalysisConfig()
        self.cp = circuit_ports or self.CircuitPorts()
        self.app = app_config or self.APPConfig()
        self.circuit = self.Circuit()

        self.net_device_map: DefaultDict[str, List[str]] = defaultdict(list)
        self.config_complete: bool = False
        self.circuit.beam_net_sets = {}

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

        # 参数存储
        self.calibrate_params: Dict[str,Dict[str,str]] = {}
        self.device_params: Dict[str, Dict[str, str]] = {}
        
        # 辅助缓存
        self.top_nodes: List['CircuitAnalyzer.Device'] = [] #存储顶层节点
        self._flat_beam_cache: Optional[List[Set[str]]] = None

    # ------------------------------
    # [P1] 日志与报告辅助函数
    # ------------------------------
    @staticmethod
    def _json_default(obj: Any) -> Any:
        """
        轻量级 JSON 序列化辅助函数。
        用于处理 set、Enum、Device 对象等非 JSON 标准类型。
        """
        if isinstance(obj, set):
            # 强制转换为排序后的列表，确保顺序一致
            return sorted(list(obj), key=str)
        if isinstance(obj, tuple):
            return list(obj)
        if isinstance(obj, Enum):
            return obj.name
        if isinstance(obj, type):
            return getattr(obj, "__name__", str(obj))
        if isinstance(obj, datetime):
            return obj.isoformat()
        if isinstance(obj, BaseException):
            return str(obj)
        # 对于 Device 或其他自定义对象，优先返回 name，否则转字符串
        if hasattr(obj, "name"):
            return obj.name
        return str(obj)
    
    def _emit(self, level: str, message: str, exc_info: Optional[Union[bool, BaseException]] = None, **context: Any) -> None:
        """
        统一事件出口：Logger (控制台) + Report (结构化存储)。
        不再进行深度递归清洗，仅做浅层序列化适配。
        """
        level_lower = (level or "info").lower()
        
        # 1. 浅层处理 Context，确保存入 Report 的数据相对干净
        safe_context = {}
        for k, v in context.items():
            # 基础类型直接保留，复杂类型用 _json_default 转换一次
            if isinstance(v, (str, int, float, bool, type(None))):
                safe_context[k] = v
            else:
                safe_context[k] = self._json_default(v)

        # 2. Logger 输出
        # 利用 logging 的 lazy evaluation，但在 context 拼接时直接转字符串
        log_fn = getattr(self.logger, level_lower, self.logger.info)
        log_suffix = f" | {json.dumps(safe_context, default=self._json_default, ensure_ascii=False)}" if safe_context else ""
        
        if exc_info:
            log_fn(f"{message}{log_suffix}", exc_info=exc_info)
        else:
            log_fn(f"{message}{log_suffix}")

        # 3. Report 记录
        # 注意：这里存入的是处理过的 safe_context
        try:
            self.report.add_event(level_lower, message, **safe_context)
        except Exception:
            pass # 避免报告写入失败影响主流程

    def _warn(self, message: str, exc_info: Optional[Union[bool, BaseException]] = None, **context: Any) -> None:
        self._emit("warning", message, exc_info=exc_info, **context)

    def _info(self, message: str, exc_info: Optional[Union[bool, BaseException]] = None, **context: Any) -> None:
        self._emit("info", message, exc_info=exc_info, **context)

    def _error(self, message: str, exc_info: Optional[Union[bool, BaseException]] = None, **context: Any) -> None:
        self._emit("error", message, exc_info=exc_info, **context)

    def export_report(self) -> Dict[str, Any]:
        """
        导出结构化报告。
        使用 json.dumps(sort_keys=True) 确保输出的确定性（顺序一致）。
        """
        raw = {
            "created_at_utc": self.report.created_at_utc,
            "stats": self.report.stats,
            "events": self.report.events,
            "calibrations": self.report.calibrations,
            "final params": self.calibrate_params
        }
        try:
            # 序列化再反序列化，确保所有对象都已转换为 JSON 标准类型
            # sort_keys=True 保证了字典 key 的排序，消除了非确定性
            json_str = json.dumps(self.calibrate_params, default=self._json_default, sort_keys=True, ensure_ascii=False)
            report_digest = hashlib.sha256(json_str.encode('utf-8')).hexdigest()
            
            raw["digest"] = report_digest
            return raw
        except Exception as e:
            return {
                "error": "Report export failed",
                "details": str(e),
                "partial_stats": self.report.stats
            }

    # ------------------------------
    # 流水线生命周期管理
    # ------------------------------
    def _reset_report_for_run(self) -> None:
        """为一次 pipeline run 重置 report（保证可重入且不累积污染）。

        设计目标：
        - 同一实例重复跑 pipeline，应得到一致的 report 结构（在全局配置不变的情况下）。
        - 保留“输入阶段”产生的统计与事件（例如入口告警），作为基线审计信息。
        - 每次 run 的规则执行信息、校准信息等应从基线重新生成，避免累计。
        """
        if self._baseline_report is None:
            base_stats: Dict[str, Any] = {}
            for k, v in dict(self.report.stats).items():
                if str(k).startswith("input_") or k in ("config_complete",):
                    base_stats[k] = v
            self._baseline_report = {
                "events": list(self.report.events),
                "calibrations": list(self.report.calibrations),
                "stats": base_stats}

        base = self._baseline_report

        self.report.events = list(base.get("events", []))
        self.report.calibrations = list(base.get("calibrations", []))
        self.report.stats = dict(base.get("stats", {}))

    def _reset_derived_state_for_run(self) -> None:
        """
        清理所有派生状态 (Derived State)，保留核心事实 (Source of Truth)。
        SoT 包括: devices_dict, net_device_map, device_params。
        """
        # 1. 清理图驱动存储
        self.tag_index.clear()
        self.relation_graph.clear()
        self.device_groups.clear()

        # 2. 清理 Circuit 派生属性
        self.circuit.substructures.clear()
        self.circuit.current_paths.clear()
        self.circuit.current_beams.clear()
        self.circuit.current_beam_paths.clear()
        self.circuit.beam_net_sets.clear()

        # 3. 清理器件对象内部状态
        for dev in self.circuit.devices_dict.values():
            dev.tags.clear()
            dev.substructures.clear()

        # 4. 清理其他缓存
        self.constraint_groups = []
        self.copy_tube_r_raw_map.clear()
        self.calibrate_params.clear()
        self.top_nodes = []
        self._flat_beam_cache = None

    def _record_state_snapshot(self, stage: str) -> None:
        """
        记录轻量级状态快照 (仅统计数量)。
        用于快速诊断流程中数据规模的变化。
        """
        # 简单开关控制
        if not os.getenv("ANALYZER_RECORD_SNAPSHOTS"):
            return

        snapshot = {
            "stage": stage,
            "devices": len(self.circuit.devices_dict),
            "tags_idx_count": len(self.tag_index),
            "groups_count": len(self.device_groups),
            "relations_src_count": len(self.relation_graph),
            "substructures": len(self.circuit.substructures),
            "paths": len(self.circuit.current_paths),
            "beams": len(self.circuit.current_beams)
        }
        
        if "snapshots" not in self.report.stats:
            self.report.stats["snapshots"] = []
        self.report.stats["snapshots"].append(snapshot)

    def _validate_state(self, stage: str) -> None:
        """
        运行期完整性校验 (精简版)。
        仅检查引用完整性：索引中的名称是否真实存在于器件字典中。
        """
        # 简单开关控制
        if not os.getenv("ANALYZER_VALIDATE_STATE"):
            return

        errors = []

        # 1. 检查 Tag Index 引用
        for tag, names in self.tag_index.items():
            for name in names:
                if name not in self.circuit.devices_dict:
                    errors.append(f"[Tag] '{tag}' references missing device '{name}'")

        # 2. 检查 Group 引用
        for group_key, group_lists in self.device_groups.items():
            for members in group_lists:
                for name in members:
                    if name not in self.circuit.devices_dict:
                        errors.append(f"[Group] '{group_key}' references missing device '{name}'")

        # 3. 检查 Relation 引用
        for src, rels in self.relation_graph.items():
            if src not in self.circuit.devices_dict:
                errors.append(f"[Rel] Source '{src}' is missing")
            for rel_key, targets in rels.items():
                for dst in targets:
                    if dst not in self.circuit.devices_dict:
                        errors.append(f"[Rel] '{src}' -> '{rel_key}' -> missing target '{dst}'")

        if errors:
            self._warn(f"State validation failed at {stage}", count=len(errors), errors=errors[:5])

    def _prepare_for_pipeline_run(self) -> None:
        """流水线启动前准备"""
        self._reset_report_for_run()
        self._reset_derived_state_for_run()
        self._record_state_snapshot("pipeline_start")

    def _finalize_pipeline_run(self) -> None:
        """流水线结束后收尾"""
        self._record_state_snapshot("pipeline_end")
        self._validate_state("pipeline_end")


    @classmethod
    def from_parsed_data(cls, devices_information: List[List[Any]], config_complete: bool, app_config: Optional[APPConfig] = None):
        """
        校验网表解析数据，实例化Device，创建分析器

        验证契约（由APPConfig强制执行）：
        - devices_information[i][1] 必须等于 APPConfig.ALIAS_CONFIG[identifier]
        - devices_information[i][2] 的键必须是 APPConfig.PORT_CONFIG[identifier] 的子集
        - devices_information[i][3] 的键必须是 APPConfig.PARAM_CONFIG[identifier] 的子集
        """
        analyzer = cls(app_config = app_config)
        analyzer.config_complete = config_complete

        # [P1] 记录输入统计与配置状态
        try:
            analyzer.report.stats.update({
                "input_device_count": len(devices_information) if isinstance(devices_information, list) else None,
                "config_complete": bool(config_complete),
            })
        except Exception:
            pass
        if not config_complete:
            analyzer._warn("入口标志 config_complete=False，将跳过参数校准")

        
        if not isinstance(devices_information, list):
            raise TypeError("devices_information必须是列表")

        # APPConfig验证
        for idx, dev_info in enumerate(devices_information):
            if not isinstance(dev_info, (list, tuple)):
                raise TypeError(f"器件信息格式错误（索引{idx}）: 期望list/tuple，实际{type(dev_info).__name__}")

            if len(dev_info) != 4:
                raise ValueError(f"器件信息格式错误（索引{idx}）: 期望4元素，实际{len(dev_info)}")

            name, dev_type_str, terminals, params = dev_info

            if not isinstance(name, str) or not name:
                raise TypeError(f"器件信息格式错误（索引{idx}）: name 必须为非空字符串")

            if not isinstance(dev_type_str, str) or not dev_type_str:
                raise TypeError(f"器件 '{name}' 类型字段必须为非空字符串")
            if name in analyzer.circuit.devices_dict:
                raise ValueError(f"器件名重复（索引{idx}）: '{name}'")

            # 验证器件类型引用格式
            identifier = analyzer.app.get_identifier_by_type(dev_type_str)

            # 验证端口配置与格式
            if not isinstance(terminals, dict):
                raise TypeError(f"器件 '{name}' terminals 必须为 dict，实际{type(terminals).__name__}")

            bad_port_keys = [k for k in terminals.keys() if not isinstance(k, str)]
            if bad_port_keys:
                raise TypeError(f"器件 '{name}' 端口名必须为字符串，非法键: {bad_port_keys!r}")

            bad_port_vals = {k: v for k, v in terminals.items() if not isinstance(v, str)}
            if bad_port_vals:
                raise TypeError(f"器件 '{name}' 端口值必须为字符串(net名)，非法项: {bad_port_vals!r}")

            legal_ports = analyzer.app.get_legal_ports(identifier)
            ports_set = set(terminals.keys())
            if not ports_set.issubset(legal_ports):
                illegal_ports = sorted(ports_set - set(legal_ports))
                raise ValueError(f"器件 '{name}' 端口非法: {illegal_ports}")

            # 验证参数类型与格式
            if not isinstance(params, dict):
                raise TypeError(f"器件 '{name}' params 必须为 dict，实际{type(params).__name__}")

            bad_param_keys = [k for k in params.keys() if not isinstance(k, str)]
            if bad_param_keys:
                raise TypeError(f"器件 '{name}' 参数名必须为字符串，非法键: {bad_param_keys!r}")

            legal_params = analyzer.app.get_legal_params(identifier)
            param_set = set(params.keys())
            if not param_set.issubset(legal_params):
                illegal_params = sorted(param_set - set(legal_params))
                raise ValueError(f"器件 '{name}' 参数非法: {illegal_params}")
            
        
            # 验证通过，Device实例化
            # [隔离] 防止外部 dict 继续被修改影响分析器状态
            params_copy = copy.deepcopy(params)
            analyzer.device_params[name] = params_copy

            terminals_lower = {k: v.lower() for k, v in terminals.items()}

            # 2. 创建Device实例并存入字典
            device_obj = cls.Device(
                name=name,
                type=dev_type_str,
                terminals=terminals_lower,
                params=params_copy
            )
            analyzer.circuit.devices_dict[name] = device_obj

            # 构建网络-器件映射
            nets = set(terminals_lower.values())  # 避免重复添加
            for net in nets:
                analyzer.net_device_map[net].append(name)

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
        # 1. [关键] 在解析前，先实例化配置对象
        # 这里的 cls.APPConfig 引用的是类定义，用来实例化
        config_instance = cls.APPConfig()

        # 选择解析器
        if parser_class is None:
            parser_class = cls.DefaultSpiceParser
        
        # 解析网表
        parser = parser_class(netlist_path,app_config=config_instance)
        devices_info = parser.parse()
        
        # 自动检测配置完整性
        config_complete = parser.check_config_complete()
        
        # 使用统一入口创建
        return cls.from_parsed_data(
            devices_info,
            config_complete=config_complete,
            app_config = config_instance
        )
    
    # ==================== 默认网表解析器 ====================
    class DefaultSpiceParser:
        """
        默认 Spectre/SPICE 网表解析器（面向本分析器的“入口 IR”）。

        设计目标：
        - 仅解析分析器工作域内的器件：MOS / Resistor / Capacitor；
        - 忽略 isource/vsource 等激励源与其他非目标器件；
        - 若器件缺少分析器所需参数，则忽略该器件；
        - 解析 Spectre 常见的续行格式：行尾 '\\' 与下一行缩进续写。

        支持的实例语法（与示例网表一致）：
        - MOS:  <NAME> (<D> <G> <S> <B>) <MODEL> w=<W_TOTAL> l=<L> nf=<NF> ...
                其中 MODEL 以 'p'/'n'（大小写均可）开头决定 PMOS/NMOS
                且 w 为总宽度，分析器参数 fw 需计算：fw = w / nf，m = nf
        - RES:  <NAME> (<PLUS> <MINUS>) resistor r=<R> l=<L> w=<W> ...
                分析器参数：segL=l, segW=w
        - CAP:  <NAME> (<PLUS> <MINUS>) capacitor c=<C> l=<L> ...
                分析器参数：l=l
        """

        # 可按需扩展的忽略类型
        IGNORE_TYPES = {"isource", "vsource"}

        # instance 行的粗匹配：NAME (nets...) token3 rest...
        _INST_RE = re.compile(
            r"^\s*([A-Za-z0-9_]+)\s*\(([^)]*)\)\s*([A-Za-z0-9_]+)\s*(.*)$"
        )

        # key=value 解析（值不含空白）
        _KV_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*([^\s]+)")

        def __init__(
            self,
            netlist_path: str,
            app_config: 'CircuitAnalyzer.APPConfig',
            *,
            strict: bool = False,
            calibration_config: Optional[CalibrationConfig] = None,
        ):
            self.netlist_path = netlist_path
            self.app_config = app_config
            self.strict = strict
            self.calibration_config = calibration_config or CalibrationConfig()
            self.devices_info: List[List[Any]] = []

        # ------------------------------
        # Public API
        # ------------------------------
        def parse(self) -> List[List[Any]]:
            """解析网表文件并生成 devices_information（from_parsed_data 入口格式）"""
            self.devices_info = []

            logical_lines = self._read_logical_lines(self.netlist_path)
            for idx, line in enumerate(logical_lines, 1):
                try:
                    dev_info = self._parse_instance_line(line)
                    if dev_info is not None:
                        self.devices_info.append(dev_info)
                except Exception as e:
                    if self.strict:
                        raise ValueError(f"解析失败(逻辑行{idx}): {line}\n错误: {e}") from e
                    logger.warning("解析失败(已跳过): %s | error=%s", line, e)

            return self.devices_info

        def check_config_complete(self) -> bool:
            """
            检查解析出的器件是否满足分析器入口契约：
            - type 必须是 APPConfig.ALIAS_CONFIG 中的值
            - params 必须覆盖该类型在 APPConfig.PARAM_CONFIG 中声明的全部参数
            注意：本解析器已在 parse 阶段过滤缺参器件，因此通常为 True（若 devices_info 非空）。
            """
            if not self.devices_info:
                return False

            for name, dev_type, terminals, params in self.devices_info:
                identifier = self.app_config.get_identifier_by_type(dev_type)
                required_params = self.app_config.get_legal_params(identifier)
                for rp in required_params:
                    if params.get(rp, "") == "":
                        logger.warning("参数不完整: 器件 %s 的 %s 为空", name, rp)
                        return False

                # 端口键合法性（入口 from_parsed_data 也会二次校验，这里做轻量防御）
                required_ports = self.app_config.get_legal_ports(identifier)
                if not set(terminals.keys()).issubset(required_ports):
                    logger.warning("端口不完整或非法: 器件 %s", name)
                    return False

            return True

        # ------------------------------
        # Internal helpers
        # ------------------------------
        @classmethod
        def _read_logical_lines(cls, netlist_path: str) -> List[str]:
            """
            读取文件并合并 Spectre 续行：
            - 行尾 '\\' 代表续行
            - 行首 '+'（兼容部分 SPICE 写法）代表续行
            同时过滤：
            - 空行、'*' 注释行、'//' 注释行
            """
            logical: List[str] = []
            buf: List[str] = []

            def flush():
                if buf:
                    logical.append(" ".join(buf).strip())
                    buf.clear()

            with open(netlist_path, "r", encoding="utf-8") as f:
                for raw in f:
                    line = raw.strip()
                    if not line:
                        continue
                    if line.startswith("*") or line.startswith("//"):
                        continue

                    # 兼容 '+' 续行（若上一行未以 '\\' 结尾，也允许 '+' 直接续写）
                    if line.startswith("+"):
                        line = line[1:].strip()

                    cont = False
                    if line.endswith("\\"):
                        cont = True
                        line = line[:-1].rstrip()

                    buf.append(line)
                    if not cont:
                        flush()

            flush()
            return [ln for ln in logical if ln]

        def _parse_instance_line(self, line: str) -> Optional[List[Any]]:
            """解析单个逻辑行；非实例行或被忽略类型返回 None。"""
            m = self._INST_RE.match(line)
            if not m:
                return None

            name, nets_blob, token3, rest = m.groups()
            nets = [n for n in nets_blob.split() if n]
            token3_l = token3.lower()

            # 1) resistor/capacitor/isource/vsource
            if token3_l in self.IGNORE_TYPES:
                return None

            if token3_l == "resistor":
                return self._build_resistor(name, nets, rest)
            if token3_l == "capacitor":
                return self._build_capacitor(name, nets, rest)

            # 2) MOS：由 model token3 决定类型（p*/n*）
            model = token3
            if model and model[0].lower() in {"p", "n"}:
                return self._build_mos(name, nets, model, rest)

            # 其他类型：忽略
            return None

        def _extract_kv(self, rest: str) -> Dict[str, str]:
            """提取 key=value 键值对（key 统一为小写），值保留原字符串。"""
            kv: Dict[str, str] = {}
            for k, v in self._KV_RE.findall(rest or ""):
                kv[k.lower()] = v
            return kv

        @staticmethod
        def _parse_number(val_str: str) -> Optional[float]:
            """解析工程/科学计数法数值为 float（不带维度约束）。"""
            if val_str is None:
                return None
            s = str(val_str).strip()
            if s == "":
                return None
            s_lower = s.lower()

            multipliers = {
                "f": 1e-15, "p": 1e-12, "n": 1e-9, "u": 1e-6, "m": 1e-3,
                "k": 1e3, "meg": 1e6, "g": 1e9
            }

            mm = re.match(
                r"^\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)\s*([a-zA-Z]+)?\s*$",
                s_lower,
            )
            if not mm:
                return None

            num_part, suffix = mm.groups()
            try:
                value = float(num_part)
            except ValueError:
                return None

            if suffix:
                suffix = suffix.lower()
                if suffix in multipliers:
                    value *= multipliers[suffix]
                else:
                    # 未知后缀：按无后缀处理
                    pass
            return value

        def _format_length(self, value_m: float) -> str:
            """
            将米值格式化为分析器常用字符串（u / n）。
            注意：此处仅用于 parser 生成 fw（以及可选的归一化输出），不进行 10nm 网格量化。
            """
            if value_m == 0.0:
                return "0"
            if abs(value_m) >= self.calibration_config.micro_threshold_m:
                v = round(value_m * 1e6, self.calibration_config.micro_decimals)
                s = f"{v}u"
                # 去掉尾随 .0
                s = s.replace(".0u", "u")
                return s
            else:
                v = int(round(value_m * 1e9))
                return f"{v}n"

        def _build_mos(self, name: str, nets: List[str], model: str, rest: str) -> Optional[List[Any]]:
            # 端口必须为 4
            if len(nets) != 4:
                return None

            kv = self._extract_kv(rest)

            # 必需参数：w / l / nf
            w_s = kv.get("w")
            l_s = kv.get("l")
            nf_s = kv.get("nf")
            if not (w_s and l_s and nf_s):
                return None

            w_total = self._parse_number(w_s)
            nf_val = self._parse_number(nf_s)
            if w_total is None or nf_val is None:
                return None

            nf_int = int(round(nf_val))
            if nf_int <= 0:
                return None

            fw = w_total / nf_int
            fw_str = self._format_length(fw)

            # type 由 model 首字母决定
            mos_identifier = "PMOS" if model[0].lower() == "p" else "NMOS"
            dev_type = self.app_config.get_device_alias(mos_identifier)

            terminals = {"D": nets[0], "G": nets[1], "S": nets[2], "B": nets[3]}
            params = {"l": l_s, "fw": fw_str, "m": str(nf_int)}

            # 若缺少分析器所需参数（理论上不会到这里），则忽略
            required = self.app_config.get_legal_params(mos_identifier)
            if not required.issubset(params.keys()):
                return None

            return [name, dev_type, terminals, params]

        def _build_resistor(self, name: str, nets: List[str], rest: str) -> Optional[List[Any]]:
            if len(nets) != 2:
                return None

            kv = self._extract_kv(rest)
            l_s = kv.get("l")
            w_s = kv.get("w")
            if not (l_s and w_s):
                return None

            identifier = "RESISTOR"
            dev_type = self.app_config.get_device_alias(identifier)
            terminals = {"PLUS": nets[0], "MINUS": nets[1]}
            params = {"segL": l_s, "segW": w_s}

            required = self.app_config.get_legal_params(identifier)
            if not required.issubset(params.keys()):
                return None

            return [name, dev_type, terminals, params]

        def _build_capacitor(self, name: str, nets: List[str], rest: str) -> Optional[List[Any]]:
            if len(nets) != 2:
                return None

            kv = self._extract_kv(rest)
            l_s = kv.get("l")
            if not l_s:
                return None

            identifier = "CAPACITOR"
            dev_type = self.app_config.get_device_alias(identifier)
            terminals = {"PLUS": nets[0], "MINUS": nets[1]}
            params = {"l": l_s}

            required = self.app_config.get_legal_params(identifier)
            if not required.issubset(params.keys()):
                return None

            return [name, dev_type, terminals, params]
    
    def _run_analysis_pipeline(self):
        """
        执行分析流程（P2：声明式规则 pipeline）

        - 将原先硬编码的顺序调用重构为 AnalysisRule 列表；
        - 每条规则具备名称、前置条件、可选性与描述，便于扩展与审计；
        - 解析器相关（SPICE -> IR）不在本轮 P2 范围内。
        """
        # [Audit] 允许实例重复运行：每次运行前清理派生态与报告
        self._prepare_for_pipeline_run()

        rules = self._build_default_rules()
        self._run_rules(rules)

        self._finalize_pipeline_run()

    def _build_default_rules(self) -> List[AnalysisRule]:
        """
        构建默认分析规则列表（高精度依赖版）。
        
        优化策略：
        requires 字段详细列出了该函数执行所需的具体数据结构。
        格式: ((属性路径, 类型), ...)
        
        依赖项说明:
        - circuit.devices_dict: 基础器件库 (Data)
        - net_device_map: 网络拓扑索引 (Data)
        - top_nodes: 顶层节点缓存 (Data)
        - tag_index: 标签索引 (Tags) -> 用于查找特定角色的器件
        - relation_graph: 关系图谱 (Relations) -> 用于查找镜像/级联关系
        - circuit.current_paths: 原始电流路径 (Paths)
        - circuit.current_beams: 聚类后的电流束 (Beams)
        - circuit.beam_net_sets: 电流束内部网络 (Beams Data)
        - device_groups: 器件分组 (Groups)
        """
        def r(name, func, reqs, desc, opt=False):
            # 统一转为 tuple
            if isinstance(reqs, str): reqs = (reqs,)
            return AnalysisRule(name, func, tuple(reqs), opt, desc)

        # 依赖路径简写
        DEVS = "circuit.devices_dict"
        NETS = "net_device_map"
        TAGS = "tag_index"
        RELS = "relation_graph"
        PATHS = "circuit.current_paths"
        BEAMS = "circuit.current_beams"
        
        return [
            # --- Phase 1: 基础标记与拓扑识别 ---
            r("mark_obvious", "_mark_obvious_tags", DEVS, "标记基础Tag:二极管/顶层/差分"),
            r("mark_outports", "_mark_outport_devices", NETS, "标记输出端管/RC结构"),
            r("mark_cm_detect_b", "_mark_common_mode_detect_b", TAGS, "识别4管共模检测", opt=True),
            r("analyze_diode_structs", "_analyze_diode_mos_structures", TAGS, "构建二极管级联/镜像关系"),
            r("mark_root_ref", "_mark_root_reference_path", TAGS, "追踪根参考管", opt=True),
            r("detect_lv_mirrors", "_detect_low_voltage_current_mirrors", DEVS, "识别低压电流镜关系", opt=True),

            # --- Phase 2: 全局路径与电流束 ---
            r("gen_paths", "generate_current_paths", "top_nodes", "生成电流路径"),
            r("analyze_beams", "analyze_current_beams", PATHS, "聚类生成电流束"),
            r("mark_bias", "_mark_bias_mirrors", BEAMS, "标记偏置管", opt=True),

            # --- Phase 3: 子结构登记 (关系驱动 & 电流束驱动) ---
            r("reg_std_mirrors", "_register_current_mirrors", RELS, "登记普通电流镜", opt=True),
            r("reg_lv_mirrors", "_register_lv_mirrors", RELS, "登记低压电流镜", opt=True),
            r("reg_rc_structs", "_register_rc_structures", TAGS, "登记RC结构", opt=True),
            
            r("reg_beam_structs", "_register_beam_substructures", "circuit.current_beam_paths", "登记差分/负载/跨束结构", opt=True),
            r("reg_lv_pairs", "_register_lv_mirror_pairs", BEAMS, "登记低压镜像对", opt=True),
            r("reg_sym_caps", "_register_sym_capacitors", "circuit.current_beam_paths", "登记对称电容", opt=True),
            
            r("get_tail", "_get_tail_current", "circuit.current_beam_paths", "识别尾电流源", opt=True),
            r("get_out_pair", "_get_output_pair", "circuit.beam_net_sets", "聚类逻辑输出对", opt=True),

            # --- Phase 4: 校准与输出 ---
            r("gen_constraints", "_generate_constraint_groups", "circuit.substructures", "生成参数约束组", opt=True),
            r("calibrate", "_maybe_calibrate", "device_params", "执行参数校准", opt=True),
            r("normalize", "_normalize_outputs_deterministically", (), "产物归一化", opt=True),
        ]

    def _run_rules(self, rules: List[AnalysisRule]) -> None:
        """运行规则列表，并将执行情况写入 report.stats。"""
        executed: List[str] = []
        skipped: List[Dict[str, Any]] = []
        failed: List[Dict[str, Any]] = []

        for rule in rules:
            # 1. 检查前置数据依赖
            missing = self._check_rule_requires(rule.requires)
            if missing:
                rec = {"rule": rule.name, "reason": "missing_requires", "missing": missing}
                if rule.optional:
                    self._warn("规则跳过(依赖缺失)", **rec)
                    skipped.append(rec)
                else:
                    self._error("规则失败(依赖缺失)", **rec)
                    failed.append(rec)
                continue

            # 2. 获取函数
            func = getattr(self, rule.func_name, None)
            if not func:
                rec = {"rule": rule.name, "reason": "func_not_found", "func": rule.func_name}
                self._error("规则失败(函数缺失)", exc_info = True, **rec)
                failed.append(rec)
                continue

            # 3. 执行
            self._info("执行规则", rule=rule.name)
            try:
                func()
                executed.append(rule.name)
            except Exception as e:
                # 仅在异常时获取 traceback，避免性能损耗
                tb = traceback.format_exc()
                rec = {"rule": rule.name, "reason": "exception", "error": str(e)}
                self._error("规则执行异常", exc_info = True, traceback=tb, **rec)
                failed.append(rec)

        # 更新报告统计
        self.report.stats.update({
            "rules_total": len(rules),
            "rules_executed": executed,
            "rules_skipped": skipped,
            "rules_failed": failed,
        })

    def _check_rule_requires(self, requires: Tuple[str, ...]) -> List[str]:
        """
        检查属性路径是否存在且非空。
        支持 'a.b' 嵌套路径。
        """
        missing = []
        for path in requires:
            if not path: continue
            
            val = self
            try:
                for part in path.split('.'):
                    val = getattr(val, part)
            except AttributeError:
                val = None
            
            # 判定标准：值为 None 或 空容器(list/dict/set) 视为缺失
            # 注意：False 或 0 是有效值，不应视为缺失
            is_empty = False
            if val is None:
                is_empty = True
            elif isinstance(val, (list, dict, set, tuple)) and len(val) == 0:
                is_empty = True
            
            if is_empty:
                missing.append(path)
        
        return missing

    def _maybe_calibrate(self) -> None:
        """在 config_complete 条件下执行参数校准；否则复制原参数。"""
        if self.config_complete:
            self._info("生成约束并校准参数")
            self._precompute_r_raw_map()
            self._calibrate_device_params()
        else:
            self._warn("参数配置不完整，跳过参数校准")
            self.calibrate_params = copy.deepcopy(self.device_params)

    def _normalize_outputs_deterministically(self) -> None:
        """
        [确定性] 对分析产物进行排序与去重归一化。

        目的：
        1) 消除 set 遍历与 dict 插入顺序造成的非确定性；
        2) 便于单元测试、软著材料固化输出、跨环境复现。

        注意：
        - 不改变单条路径/束内部的语义顺序（如 current_paths 的序列顺序）；
        - 仅对“容器层面的枚举顺序”做规范化。
        """
        # 1) 子结构：按 sub_id 排序；成员按名字排序；约束按字段排序
        if self.circuit.substructures:
            for sub in self.circuit.substructures:
                sub.members = sub.members
                sub.constraints = sorted(
                    sub.constraints,
                    key=lambda c: (
                        getattr(getattr(c, "type", None), "name", ""),
                        c.target_dev_name,
                        c.target_param,
                        c.source_dev_name,
                        c.source_param,
                    ),
                )
            self.circuit.substructures.sort(key=lambda s: s.sub_id)

        # 2) 约束组：组内已排序；组间按字典序排序
        if self.constraint_groups:
            self.constraint_groups = [sorted(g) for g in self.constraint_groups]
            self.constraint_groups.sort(key=lambda g: tuple(g))

        # 3) 关系图：target 列表去重并排序；外层 key 排序重建
        if self.relation_graph:
            normalized_rg: DefaultDict[str, DefaultDict[str, List[str]]] = defaultdict(lambda: defaultdict(list))
            for src in sorted(self.relation_graph.keys()):
                rels = self.relation_graph[src]
                for rel_key in sorted(rels.keys()):
                    targets = rels[rel_key]
                    # 关系本质上是集合：去重 + 排序
                    normalized_rg[src][rel_key] = sorted(set(targets))
            self.relation_graph = normalized_rg

        # 4) device_groups：仅规范“组列表”的顺序（不强制改写组内成员顺序）
        if self.device_groups:
            normalized_dg: DefaultDict[str, List[List[str]]] = defaultdict(list)
            for gk in sorted(self.device_groups.keys()):
                groups = self.device_groups[gk]
                normalized_dg[gk] = sorted(groups, key=lambda m: tuple(m))
            self.device_groups = normalized_dg

        # 5) Circuit 的电流相关产物：仅排序容器层面的枚举顺序
        if self.circuit.current_paths:
            self.circuit.current_paths = sorted(self.circuit.current_paths, key=lambda p: tuple(p))

        if self.circuit.beam_net_sets:
            self.circuit.beam_net_sets = {k: self.circuit.beam_net_sets[k] for k in sorted(self.circuit.beam_net_sets.keys())}

        # 6) 参数字典：外层器件名、内层参数名排序重建（便于稳定导出）
        if self.device_params:
            self.device_params = {
                dn: {pk: self.device_params[dn][pk] for pk in sorted(self.device_params[dn].keys())}
                for dn in sorted(self.device_params.keys())
            }

        if self.calibrate_params:
            self.calibrate_params = {
                dn: {pk: self.calibrate_params[dn][pk] for pk in sorted(self.calibrate_params[dn].keys())}
                for dn in sorted(self.calibrate_params.keys())
            }

        # 7) r_raw 真值映射：按复制管名称排序重建
        if self.copy_tube_r_raw_map:
            self.copy_tube_r_raw_map = {k: self.copy_tube_r_raw_map[k] for k in sorted(self.copy_tube_r_raw_map.keys())}

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
        return self._net_matches(net,self.cp.POWER_POSITIVE) or self._net_matches(net,self.cp.POWER_NEGATIVE)

    def _is_net_power(self, net_name: str) -> bool:
        """检查是否为正电源"""
        return self._net_matches(net_name, self.cp.POWER_POSITIVE)
    
    def _is_net_ground(self, net_name: str) -> bool:
        """检查是否为地/负电源"""
        return self._net_matches(net_name, self.cp.POWER_NEGATIVE)
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
                self._warn("尝试给不存在的器件打标签", device=device, tag=tag)
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
            self._warn("删除器件标签失败", device=device, tag=tag)

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
        AC = self.ac  # 快捷引用
        
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
                    if self._net_matches(g_net, self.cp.INPUT_POSITIVE):
                        self.add_tag(device, AC.TAG_DIFF_POS)
                    elif self._net_matches(g_net, self.cp.INPUT_NEGATIVE):
                        self.add_tag(device, AC.TAG_DIFF_NEG)

            # ------------------------ 4. 标记共模检测管 --------------------------
            if device.type in ["PMOS", "NMOS"]:
                g_net = device.terminals.get("G", "")
                if self._net_matches(g_net, self.cp.COMMON_SIGN):
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
        AC = self.ac

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
        positive_nets_lower = {n.lower() for n in self.cp.OUTPORT_POSITIVE}
        for net_name_lower in positive_nets_lower:
            device_names = self.net_device_map.get(net_name_lower, [])
            _process_output_net_devices(device_names, net_name_lower)

        negative_nets_lower = {n.lower() for n in self.cp.OUTPORT_NEGATIVE}
        for net_name_lower in negative_nets_lower:
            device_names = self.net_device_map.get(net_name_lower, [])
            _process_output_net_devices(device_names, net_name_lower)

    # ---------------------------------------------标记B型（4管）共模检测 ---------------------------------------------------
    def _mark_common_mode_detect_b(self):
        """
        如果识别到2个外侧共模管，则查找其共源极连接的另外2个内侧共模管，并一并打上4管共模检测标签

        注意：假设存在2个外侧共模管时，必然有2个共源级连接内侧共模管，否则不打共模内侧管标签与4管共模检测标签

        **依赖外侧共模管标签**
        _mark_obvious_tags() 之后调用
        """
        AC = self.ac
        
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
            self._error("共模检测识别中发现未登记的器件名称")
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
        AC = self.ac
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
        AC = self.ac
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
        AC = self.ac
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
        AC = self.ac
        
        # 1. 查找起始网络 (IREF/IIN)
        start_net = None
        start_net_device_names = []
        current_source_lower = {s.lower() for s in self.cp.CURRENT_SOURCE}

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
        AC = self.ac
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
    def _mark_low_voltage_mirrors(self, upper_ref: 'CircuitAnalyzer.Device', lower_ref: 'CircuitAnalyzer.Device',
                                  gate_net_map):
        """
        标记低压电流镜的镜像管
        """
        AC = self.ac
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
                    self._warn("LV Ref 有镜像标签但无 Diode 偏置", upper_ref=upper_ref.name)
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
            self._warn("未识别到顶层节点，无法生成电流路径")
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
        self._info("电流路径生成完成", path_count=len(all_paths))

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
        4. 除掉共模检测、输入、输出端管，包含输出端管栅极网络的长度相等的电流路径为一类电流束
        5. 除掉以上4个，包含公共器件的长度相等的电流路径为一类电流束
        6. 剩余路径不归类。

        **依赖4管共模检测标签、差分输入标签、输出端管标签、电流路径生成**
        _mark_obvious_tags()之后
        _mark_outport_devices()之后
        _mark_common_mode_detect_b() 之后
        generate_current_paths() 之后
        """
        AC = self.ac

        # 0. 确保电流路径已生成
        if not self.circuit.current_paths:
            self._warn("电流路径未生成，请先调用 generate_current_paths()")
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
            self.circuit.beam_net_sets[beam_id] = set()
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
        AC = self.ac
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
    def _register_beam_substructures(self):
        """
        [重构版] 基于电流束路径的子结构识别
        重点修正 len==4 的 5种拓扑情况处理逻辑。
        """
        AC = self.ac

        # --- 内部辅助函数 ---
        def _register_helper(members: List['CircuitAnalyzer.Device'], sub_key: str, group_key: str):
            if not members: return
            self.add_group(group_key, [d.name for d in members])
            self.aggregate_substructure(sub_key, members)

        def _check_cross_beam_symmetry(mos_a: 'CircuitAnalyzer.Device',
                                       mos_b: 'CircuitAnalyzer.Device') -> bool:
            """检查两个MOS管的栅极网络是否至少在某一个电流束的 *内部网络* 集合中"""
            g_net_a = mos_a.terminals.get("G")
            g_net_b = mos_b.terminals.get("G")
            if not g_net_a or not g_net_b:
                return False
            for beam_net_set in self.circuit.beam_net_sets.values():
                if self._net_matches(g_net_a, beam_net_set) and self._net_matches(g_net_b, beam_net_set):
                    return True
            return False

        def _check_nets_in_single_beam_set(nets: Set[str]) -> bool:
            """检查一组网络是否同时存在于某一个电流束的内部网络集合中"""
            if not nets: return False
            for beam_net_set in self.circuit.beam_net_sets.values():
                if nets.issubset(beam_net_set):
                    return True
            return False

        # --- 构建镜像管反向查找表 (复用原逻辑) ---
        mirror_to_ref_map: Dict[str, str] = {}
        for ref_name in self.relation_graph:
            if AC.REL_STD_REF2MIRROR in self.relation_graph[ref_name]:
                for m_name in self.relation_graph[ref_name][AC.REL_STD_REF2MIRROR]:
                    mirror_to_ref_map[m_name] = ref_name
        for lower_ref_name in self.relation_graph:
            if AC.REL_LV_LREF2TOKEN in self.relation_graph[lower_ref_name]:
                for m_name in self.relation_graph[lower_ref_name][AC.REL_LV_LREF2TOKEN]:
                    mirror_to_ref_map[m_name] = lower_ref_name

        # --- 主循环 ---
        processed_devices: Set[str] = set()
        
        # 4器件结构通常也是互斥的，使用专门的集合或复用 processed_devices
        # 这里复用 processed_devices 以防止拆分后的部分再次被后续逻辑错误处理

        for beam_path in self.circuit.current_beam_paths.values():
            for element_set_names in beam_path:
                count = len(element_set_names)
                
                # 跳过部分处理过的集合 (针对 len=4 的拆分情况，如果部分已处理，则不再整体处理)
                if not element_set_names.isdisjoint(processed_devices):
                    continue

                try:
                    members = [self.circuit.devices_dict[name] for name in element_set_names]
                except KeyError:
                    continue

                # ===========================================================
                # 1. 处理 4 管结构 (5种拓扑情况)
                # ===========================================================
                if count == 4:
                    # 1.0 优先登记4管共模检测，避免错误登记成一组C型负载与一组典型负载
                    if all(AC.TAG_CM_4MOS in d.tags for d in members):
                        _register_helper(members, AC.STR_CM_DETECT_B, AC.STR_CM_DETECT_B)
                        processed_devices.update(element_set_names)
                        continue
                    # 1.1 分析栅极连接性
                    g_map = defaultdict(list)
                    for d in members:
                        g = d.terminals.get("G")
                        if g: g_map[g].append(d)
                    
                    unique_g_count = len(g_map)
                    
                    # --- 情况 (4): 所有4个栅极相连 ---
                    # 动作: 登记一组典型负载
                    if unique_g_count == 1:
                        #[cite_start]# [cite: 1] 规则 2: 典型负载
                        for d in members: self.add_tag(d, AC.TAG_LOAD_TYP)
                        _register_helper(members, AC.STR_LOAD_TYPICAL, AC.STR_LOAD_TYPICAL)
                        processed_devices.update(element_set_names)
                        continue

                    # --- 情况 (1): 2管连 + 2管连 ---
                    # 动作: 登记两组独立典型负载
                    elif unique_g_count == 2 and all(len(v) == 2 for v in g_map.values()):
                        for sub_members in g_map.values():
                            for d in sub_members: self.add_tag(d, AC.TAG_LOAD_TYP)
                            _register_helper(sub_members, AC.STR_LOAD_TYPICAL, AC.STR_LOAD_TYPICAL)
                        processed_devices.update(element_set_names)
                        continue

                    # --- 情况 (2): 2管连 + 2管独立 ---
                    # 动作: 登记一组典型负载 + 一组2管C型负载
                    elif unique_g_count == 3:
                        # 找到那组连在一起的 (典型负载)
                        tied_pair = next(v for v in g_map.values() if len(v) == 2)
                        
                        # 找到剩下的两个独立的 (候选C型负载)
                        indep_members = [d for d in members if d not in tied_pair]
                        
                        # 1. 登记典型负载部分
                        for d in tied_pair: self.add_tag(d, AC.TAG_LOAD_TYP)
                        _register_helper(tied_pair, AC.STR_LOAD_TYPICAL, AC.STR_LOAD_TYPICAL)
                        
                        # 2. 登记C型负载部分 (需检查跨束对称性)
                        if len(indep_members) == 2:
                            if _check_cross_beam_symmetry(indep_members[0], indep_members[1]):
                                for d in indep_members: self.add_tag(d, AC.TAG_LOAD_C)
                                _register_helper(indep_members, AC.STR_LOAD_C, AC.STR_LOAD_C)
                        
                        processed_devices.update(element_set_names)
                        continue

                    # --- 情况 (3) & (5): 4管栅极全独立 ---
                    elif unique_g_count == 4:
                        all_gates = {d.terminals.get("G") for d in members if d.terminals.get("G")}
                        
                        # --- 情况 (3): 4个栅极都在同一个内部网络集合中 ---
                        # 动作: 登记一组4管C型负载
                        if _check_nets_in_single_beam_set(all_gates):
                            # 注意: 如果需要专门的4管Tag或Key，请修改此处，目前复用C型负载逻辑
                            for d in members: self.add_tag(d, AC.TAG_LOAD_C) # 也可以是 TAG_CM_4MOS
                            _register_helper(members, AC.STR_LOAD_C, AC.STR_LOAD_C)
                            processed_devices.update(element_set_names)
                            continue
                        
                        # --- 情况 (5): 2个在集合A，2个在集合B (A!=B) ---
                        # 动作: 登记两组2管C型负载
                        else:
                            # 尝试所有两两组合，寻找满足条件的分割
                            found_split = False
                            for pair1 in itertools.combinations(members, 2):
                                pair2 = [d for d in members if d not in pair1]
                                
                                # 检查 pair1 是否构成 C型
                                is_p1_c = _check_cross_beam_symmetry(pair1[0], pair1[1])
                                # 检查 pair2 是否构成 C型
                                is_p2_c = _check_cross_beam_symmetry(pair2[0], pair2[1])
                                
                                if is_p1_c and is_p2_c:
                                    # 登记 Pair 1
                                    for d in pair1: self.add_tag(d, AC.TAG_LOAD_C)
                                    _register_helper(list(pair1), AC.STR_LOAD_C, AC.STR_LOAD_C)
                                    # 登记 Pair 2
                                    for d in pair2: self.add_tag(d, AC.TAG_LOAD_C)
                                    _register_helper(pair2, AC.STR_LOAD_C, AC.STR_LOAD_C)
                                    
                                    processed_devices.update(element_set_names)
                                    found_split = True
                                    break # 找到一种分割即可
                            
                            if found_split:
                                continue

                # ===========================================================
                # 2. 处理 2 管结构 (互斥逻辑)
                # ===========================================================
                elif count == 2:
                    names = list(element_set_names)
                    dev_a_name = names[0]
                    dev_b_name = names[1]
                    dev_a, dev_b = self.circuit.devices_dict[names[0]], self.circuit.devices_dict[names[1]]

                    # 只处理 MOS 对
                    if dev_a.type not in ["PMOS", "NMOS"] or dev_b.type not in ["PMOS", "NMOS"]:
                        continue

                    # --- 特殊或G连接的器件对 ---
                    # 规则 1: 差分输入对
                    is_diff = (AC.TAG_DIFF_POS in dev_a.tags and AC.TAG_DIFF_NEG in dev_b.tags) or \
                                (AC.TAG_DIFF_NEG in dev_a.tags and AC.TAG_DIFF_POS in dev_b.tags)
                    if is_diff:
                        _register_helper(members, AC.STR_DIFF_PAIR, AC.STR_DIFF_PAIR)
                        processed_devices.update(element_set_names)
                        continue

                    # 规则 2: 输出端对（并不是完全独立的子结构，所以不会continue）
                    is_out = (AC.TAG_OUTPORT_POS in dev_a.tags and AC.TAG_OUTPORT_NEG in dev_b.tags) or \
                                (AC.TAG_OUTPORT_NEG in dev_a.tags and AC.TAG_OUTPORT_POS in dev_b.tags)
                    if is_out:
                        _register_helper(members, AC.STR_OUTPORT_PAIR, AC.STR_OUTPORT_PAIR)
                        processed_devices.update(element_set_names)
                        #continue

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
                        processed_devices.update(element_set_names)
                        continue
                    elif b_is_diode and is_b_ref_a:
                        self.add_tag(dev_b, AC.TAG_LOAD_A_DIO)
                        self.add_tag(dev_a, AC.TAG_LOAD_A_TYP)
                        _register_helper(members, AC.STR_LOAD_A, AC.STR_LOAD_A)
                        processed_devices.update(element_set_names)
                        continue

                    # 规则 5: B型负载 
                    if a_is_diode and b_is_diode:
                        self.add_tag(dev_a, AC.TAG_LOAD_B)
                        self.add_tag(dev_b, AC.TAG_LOAD_B)
                        _register_helper(members, AC.STR_LOAD_B, AC.STR_LOAD_B)
                        processed_devices.update(element_set_names)
                        continue

                    # 规则 6: 典型负载 (来自电流镜)
                    ref_a = mirror_to_ref_map.get(dev_a_name)
                    ref_b = mirror_to_ref_map.get(dev_b_name)
                                                    
                    if ref_a and ref_b and ref_a == ref_b:
                        self.add_tag(dev_a, AC.TAG_LOAD_TYP)
                        self.add_tag(dev_b, AC.TAG_LOAD_TYP)
                        _register_helper(members, AC.STR_LOAD_TYPICAL, AC.STR_LOAD_TYPICAL)
                        processed_devices.update(element_set_names)
                        continue

                    # 规则 7: 共模检测A
                    a_is_outer = AC.TAG_CM_OUTER in dev_a.tags
                    b_is_outer = AC.TAG_CM_OUTER in dev_b.tags
                    
                    if a_is_outer != b_is_outer: # XOR
                        self.add_tag(dev_a, AC.TAG_CM_2MOS)
                        self.add_tag(dev_b, AC.TAG_CM_2MOS)
                        
                        inner = dev_b if a_is_outer else dev_a
                        self.add_tag(inner, AC.TAG_CM_INNER)
                        
                        _register_helper(members, AC.STR_CM_DETECT_A, AC.STR_CM_DETECT_A)
                        processed_devices.update(element_set_names)
                        continue

                    # --- 非 G-连接的对称负载 ---
                    g_a = dev_a.terminals.get("G")
                    g_b = dev_b.terminals.get("G")
                    if g_a and g_b and g_a != g_b:
                        if _check_cross_beam_symmetry(dev_a, dev_b):
                            self.add_tag(dev_a, AC.TAG_LOAD_C)
                            self.add_tag(dev_b, AC.TAG_LOAD_C)
                            _register_helper(members, AC.STR_LOAD_C, AC.STR_LOAD_C)
                            processed_devices.update(element_set_names)
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
        AC = self.ac

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
        AC = self.ac

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
        
        **要在识别低压电流镜(去耦合)后调用**
        _detect_low_voltage_current_mirrors之后
        """
        AC = self.ac
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
        AC = self.ac
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
        识别并聚类输出对 (Output Pair)。
        定义：对于一个输出端对，如果这两个管子的栅极网络在第一个电流束 (beam_2_differential)
        的电流束网络集合中，则它们构成输出对。

        **要在识别电流束之后调用**
        _analyze_current_beams 之后
        """
        # 1. 获取第一个电流束的网络集合
        # 对应 "beam_net_sets中第一个键的值"
        AC = self.ac

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
        AC = self.ac

        # 1. 登记 频率补偿
        # [Refactor] 直接查询拥有 COMPENSATE 标签的所有器件
        # 频率补偿
        comp_members = self.get_devices_by_tag(AC.TAG_COMPENSATE)
        comp_names = []
        for member in comp_members:
            comp_name = member.name
            comp_names.append(comp_name)
        if comp_members:
            self.add_group(AC.STR_FREQ_COMPENSATE,comp_names)
            self.aggregate_substructure(AC.STR_FREQ_COMPENSATE, comp_members)

        # RC 共模检测
        rc_cm_members = self.get_devices_by_tag(AC.TAG_RC_CM_DETECT)
        rc_cm_names = []
        for member in rc_cm_members:
            rc_cm_name = member.name
            rc_cm_names.append(rc_cm_name)
        if rc_cm_members:
            self.add_group(AC.STR_RC_CM_DETECT,rc_cm_names)
            self.aggregate_substructure(AC.STR_RC_CM_DETECT, rc_cm_members)

    # -------------------------------------------登记对称电容-------------------------------------------
    def _register_sym_capacitors(self):
        """
        遍历所有未被分配的电容, 检查对称性。
        规则：电容信号端连接的MOS管处在至少一个同一个电流束中。

        **要在标记输出端器件、识别电流束后调用**
        _mark_outport_devices 之后
        _analyze_current_beams之后
        """
        AC = self.ac

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
        # [确定性] 子结构成员按名称排序，避免 set/遍历顺序导致的非确定性
        members = sorted(members, key=lambda d: d.name)

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
            constraints = sub_def.constraint_generator(members,self.ac)
        except Exception as e:
            tb = traceback.format_exc()
            self._error("约束生成异常", exc_info=True, struct_key=struct_key, error=str(e), traceback=tb)
            constraints = []

        # 5. 存储到 Circuit
        # 注意: CircuitSub.constraints 现在存储 List[Constraint] 对象
        self.circuit.substructures.append(self.CircuitSub(
            sub_id=sub_id,
            type=struct_key, 
            members=sorted([d.name for d in members]),
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
                # 比例类约束不参与强相等分组（由独立阶段处理）
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

    # -----------------------------------------------------参数校准辅助函数 -----------------------------------------------------------
    def _parse_value_to_float(self, val_str: str, key: Optional[str] = None) -> Optional[float]:
        """
        将工程/科学计数法字符串解析为浮点数。
        支持：
        - 科学计数法：1e-6, -2.5E+3
        - 工程后缀：10u, 805n, 1k, 2meg, 3g
        - 混合空白：' 1.2u '

        同时执行基础维度约束：
        - key='m'：要求正整数（可容忍输入为浮点但会规范化为整数）
        - key in {'l','fw','segL','segW'}：要求正数（可配置开关）
        """
        if val_str is None:
            return None
        s = str(val_str).strip()
        if s == "":
            return None

        s_lower = s.lower()
        multipliers = {
            'f': 1e-15, 'p': 1e-12, 'n': 1e-9, 'u': 1e-6, 'm': 1e-3,
            'k': 1e3, 'meg': 1e6, 'g': 1e9
        }

        # 先匹配科学计数法数值，再提取可选工程后缀（后缀不含空格）
        m = re.match(r'^\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)\s*([a-zA-Z]+)?\s*$', s_lower)
        if not m:
            self._warn("无法解析参数值", value=s)
            return None

        num_part, suffix = m.groups()
        try:
            value = float(num_part)
        except ValueError:
            self._warn("无法解析参数数值部分", value=s, number=num_part)
            return None

        if suffix:
            suffix = suffix.lower()
            # 'meg' 优先于 'm'
            if suffix in multipliers:
                value *= multipliers[suffix]
            else:
                self._warn("未知工程后缀，按无后缀处理", value=s, suffix=suffix)

        k = (key or "").lower()
        if k == 'm':
            if self.calibration_config.require_positive_multiplier and value <= 0:
                self._warn("乘数参数 m 必须为正", value=s, parsed=value)
                return None
            # 规范化为整数（软著复现：一律向最近整数）
            int_val = int(round(value))
            if abs(value - int_val) > 1e-6:
                self._warn("乘数参数 m 不是整数，已规范化", value=s, parsed=value, normalized=int_val)
            return float(int_val)

        if k in {'l', 'fw', 'segl', 'segw'}:
            if self.calibration_config.require_positive_length and value <= 0:
                self._warn("几何参数必须为正", key=key, value=s, parsed=value)
                return None

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
        grid_step = self.calibration_config.grid_step_m
        rounded_value = round(value / grid_step) * grid_step

        if rounded_value == 0.0:
            return "0"

        # 规则 3: 格式化 (优先 'u', 但 < 1u 时回退到 'n')
        if abs(rounded_value) >= self.calibration_config.micro_threshold_m:  # 约 1.0u
            val_in_u = rounded_value * 1e6
            rounded_mantissa = round(val_in_u, self.calibration_config.micro_decimals)  # 'u' 小数位数可配置
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
            self._warn("无法解析或找到参数", param=param_name)
            return None

    def _set_param_val(self, param_name: str, value: str, params_dict: Dict, log_prefix=""):
        """ 辅助函数：向 device_params 字典中设置值，并记录更改 """
        try:
            dev, key = param_name.rsplit("_", 1)
            if dev not in params_dict or key not in params_dict[dev]:
                self._warn("尝试设置不存在的参数", param=param_name)
                return

            old_val = params_dict[dev][key]
            if old_val != value:
                self._info("参数校准", param=param_name, old=old_val, new=value)
                try:
                    self.report.add_calibration(param_name, old_val, value)
                except Exception:
                    pass
                params_dict[dev][key] = value
        except (KeyError, ValueError):
            self._warn("无法设置参数", param=param_name)

    def _is_copy_tube(self, target_dev: 'CircuitAnalyzer.Device', ref_dev: 'CircuitAnalyzer.Device') -> bool:
        """
        辅助函数：检查一个 'l' 参数是否属于"复制管"。
        普通电流镜：参考管是根参考管，所有镜像管都是复制管；参考管在偏置电路不是根参考管，所有非偏置镜像管是复制管；参考管在主电路，所有镜像管是复制管
        低压电流镜：下层参考管在主电路，所有镜像管是复制管；下层参考管在偏置电路，所有非偏置镜像管是复制管

        """
        AC = self.ac

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
                self._warn("W/L 计算缺少参数", device=dev_name, missing=["fw","m","l"])
                return None

            fw = self._parse_value_to_float(fw_str, 'fw')
            m = self._parse_value_to_float(m_str, 'm')  # 规范化为整数（浮点返回）
            l = self._parse_value_to_float(l_str, 'l')
            if fw is None or m is None or l is None:
                self._warn("W/L 参数解析失败", device=dev_name, fw=fw_str, m=m_str, l=l_str)
                return None

            if l == 0.0 or l is None or fw is None:
                self._warn("W/L 参数解析失败或 l=0", device=dev_name, fw=fw_str, m=m_str, l=l_str)
                return None

            return (fw * m) / l
        except (KeyError, ValueError, TypeError) as e:
            self._warn("W/L 计算异常", device=dev_name, error=str(e))
            return None

    def _precompute_r_raw_map(self):
        """
        在任何校准发生前，遍历所有电流镜，计算并存储所有“复制管”
        相对于其参考管的 *原始* W/L 比例 (r_raw)。
        修正：LV 镜的上层和下层管必须使用各自的 W/L 参考。

        这里存在逻辑冗余
        """
        AC = self.ac

        self._info("预计算 r_raw 真值开始")
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
                    self._info("r_raw 预计算: STD", copy=m_name, ref=ref_name, r_raw=round(r_raw, 8))

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
                    self._info("r_raw 预计算: LV", copy=t_name, ref=target_ref_name, r_raw=round(r_raw, 8))

        self._info("r_raw 预计算完成")

    # ----------------------------------------------------- 两阶段校准 -----------------------------------------------------------
    def _calibrate_device_params(self):
        """主入口：协调两阶段校准"""
        AC = self.ac
        # 准备工作
        new_device_params = copy.deepcopy(self.device_params)
        
        # 阶段一：应用强相等约束 (允许污染)
        self._apply_phase1_constraints(new_device_params)
        
        # 阶段二：基于 r_raw 补偿 (拨乱反正)
        self._apply_phase2_compensation(new_device_params)

        self.calibrate_params = new_device_params

    def _apply_phase1_constraints(self, params_dict: Dict):
        """阶段一：遍历所有约束组，寻找黄金标准并应用"""
        AC = self.ac
        groups = self.constraint_groups
        
        TAG_PRIORITY = [AC.TAG_ROOT_REF, AC.TAG_STD_MIRROR_REF, AC.TAG_LV_LOWER_REF, AC.TAG_CASCODE_MAIN]

        for group in groups:
            if not group: continue
            
            # 1. 寻找黄金标准 (Golden Reference)
            golden_param, golden_val = self._find_golden_value(group, params_dict, TAG_PRIORITY)
            if golden_val is None: continue

            # 2. 判断是否受保护 (Reference Is Mirror Ref?)
            is_ref_protected = False
            if golden_param:
                dev_name = golden_param.rsplit("_", 1)[0]
                tags = self.circuit.devices_dict[dev_name].tags
                if AC.TAG_STD_MIRROR_REF in tags or AC.TAG_LV_LOWER_REF in tags:
                    is_ref_protected = True

            # 3. 应用值
            for target_param in group:
                target_dev_name = target_param.rsplit("_", 1)[0]
                # 核心逻辑：如果是受保护的参考源，且目标是复制管，则推迟（跳过）
                if is_ref_protected and target_dev_name in self.copy_tube_r_raw_map:
                    continue 
                
                self._set_param_val(target_param, golden_val, params_dict, log_prefix="  ")

    def _find_golden_value(self, group: List[str], params_dict: Dict, priority_tags: List[str]) -> Tuple[Optional[str], Optional[str]]:
        """辅助：在约束组中决策最佳参考值"""
        # 策略 A: 按标签优先级
        for tag in priority_tags:
            for param in group:
                dev_name = param.rsplit("_", 1)[0]
                if tag in self.circuit.devices_dict.get(dev_name).tags:
                    val = self._get_param_val(param, params_dict)
                    if val: return param, val
        
        # 策略 B: 平均值
        param_key = group[0].rsplit("_", 1)[-1]
        values = []
        for p in group:
            v_str = self._get_param_val(p, params_dict)
            v_float = self._parse_value_to_float(v_str, param_key)
            if v_float is not None: values.append(v_float)
        
        if values:
            avg = sum(values) / len(values)
            return None, self._format_float_to_string(avg, param_key)
            
        return None, None

    def _apply_phase2_compensation(self, params_dict: Dict):
        """阶段二：对复制管进行 r_raw 补偿"""
        # 1. 重组数据：Ref -> [CopyTubes]
        ref_map = defaultdict(list)
        for copy_dev, (ref_dev, _) in self.copy_tube_r_raw_map.items():
            ref_map[ref_dev].append(copy_dev)

        for ref_dev, copy_devs in ref_map.items():
            # 按当前参数分组 (fw, m, l)
            grouped_copies = defaultdict(list)
            for dev in copy_devs:
                p = params_dict.get(dev)
                if p: grouped_copies[(p['fw'], p['m'], p['l'])].append(dev)

            # 对每一组同参复制管进行计算
            for (fw_now, m_now, _), dev_group in grouped_copies.items():
                self._compensate_single_group(ref_dev, dev_group, fw_now, m_now, params_dict)

    def _compensate_single_group(self, ref_dev: str, dev_group: List[str], fw_now: str, m_now: str, params_dict: Dict):
        """辅助：计算单组复制管的补偿值"""
        r_raw_list = [self.copy_tube_r_raw_map[dev_name][1] for dev_name in dev_group]  #获取一组复制管的原始复制比
        r_raw_target = sum(r_raw_list) / len(r_raw_list)

        # 6. 获取参考管 *当前* (阶段一后) 的 W 和 L
        ref_fw_str = params_dict[ref_dev]['fw']
        ref_m_str = params_dict[ref_dev]['m']
        ref_l_str = params_dict[ref_dev]['l']

        ref_fw_f = self._parse_value_to_float(ref_fw_str, 'fw')
        ref_m_f = self._parse_value_to_float(ref_m_str, 'm')
        if ref_fw_f is None or ref_m_f is None:
            self._warn("参考管几何参数解析失败，无法补偿", ref=ref_dev, fw=ref_fw_str, m=ref_m_str)
            return
        W_ref_now_float = ref_fw_f * ref_m_f
        L_new_str = ref_l_str  # 目标 L = 参考管的 L

        # 7. 获取复制管 *当前* (阶段一后) 的 W
        copy_fw_f = self._parse_value_to_float(fw_now, 'fw')
        copy_m_f = self._parse_value_to_float(m_now, 'm')
        if copy_fw_f is None or copy_m_f is None:
            self._warn("复制管几何参数解析失败，跳过补偿", group=dev_group, fw=fw_now, m=m_now)
            return
        W_copy_now_float = copy_fw_f * copy_m_f

        if W_ref_now_float == 0.0:
            self._warn("参考管当前 W=0，无法补偿", ref=ref_dev)
            return

        # 8. 计算 r_now (W 的比值)
        r_now_W_ratio = W_copy_now_float / W_ref_now_float

        fw_new_str = fw_now
        m_new_str = m_now

        # 9. 检查是否需要补偿 (比较 W比值 和 目标W/L比值)
        # 数学上, 要让W_target/W_ref = r_raw_target (因为 L_new=L_ref)
        if abs(r_now_W_ratio - r_raw_target) > self.calibration_config.ratio_tolerance:
            self._info("复制管补偿需求", r_now_W=round(r_now_W_ratio, 8), r_raw_target=round(r_raw_target, 8))

            # 简单计算可知：W_target = W_ref_now * r_raw_target
            W_target = W_ref_now_float * r_raw_target

            m_target = float(m_now)
            fw_target = W_target / m_target

            # 10. 应用 DRC 感知的 fw/m 补偿逻辑
            if 0 < fw_target <= self.calibration_config.fw_case3_max_m:  # Case 3
                fw_new_str = self._format_float_to_string(fw_target, 'fw')
                m_new_str = m_now

            else:  # Case 2
                m_target_float = math.ceil(fw_target / self.calibration_config.fw_case3_max_m)
                if m_target_float > self.calibration_config.m_case1_max:  # Case 1
                    self._warn("复制管补偿失败：fw/m 均超限（Case1）", group=dev_group, m_target=int(m_target_float))
                    L_new_str = ref_l_str
                    fw_new_str = fw_now
                    m_new_str = m_now
                else:
                    m_new_int = int(m_target_float)
                    fw_final = W_target / m_new_int
                    fw_new_str = self._format_float_to_string(fw_final, 'fw')
                    m_new_str = str(m_new_int)
        else:
            self._info("复制管无需补偿", r_now_W=round(r_now_W_ratio, 8), r_raw_target=round(r_raw_target, 8))

        # 11. 应用最终值 (fw, m, l) 到组内所有管子
        for dev_name in dev_group:
            self._set_param_val(f"{dev_name}_l", L_new_str, params_dict, log_prefix="    ")
            self._set_param_val(f"{dev_name}_fw", fw_new_str, params_dict, log_prefix="    ")
            self._set_param_val(f"{dev_name}_m", m_new_str, params_dict, log_prefix="    ")

# ------------------------------
# 使用示例
# ------------------------------
if __name__ == "__main__":
    # ================= 配置区 =================
    # [请修改] 这里填写您的 SPICE 网表文件路径
    # 如果文件在同目录下，直接写文件名即可
    netlist_path = "netlist1.txt" 
    # =========================================

    print("\n" + "=" * 30 + " 测试初始化 " + "=" * 30)
    
    # 简单的文件存在检查
    if not os.path.exists(netlist_path):
        print(f"[错误] 网表文件不存在: {netlist_path}")
        print("提示: 请在脚本底部的 'netlist_path' 变量中填入有效的 SPICE 网表路径。")
        # 此时程序不会崩溃，但后续分析步骤会跳过
    else:
        try:
            # 1. 初始化分析器 (面向 SPICE 网表)
            # 内部会自动调用 from_parsed_data 并执行 _run_analysis_pipeline
            analyzer = CircuitAnalyzer.from_spice_netlist(netlist_path)
            AC = analyzer.ac  # 快捷引用配置对象

            print("\n" + "=" * 30 + " 测试输出 " + "=" * 30)

            # --- 1. 检查器件数量 ---
            print(f"\n[电路基本信息]")
            print(f"  识别到的器件总数: {len(analyzer.circuit.devices_dict)}")

            # --- 2. 检查部分器件详情 ---
            # 自动选取前5个器件进行展示，或使用默认列表
            devices_to_check = list(analyzer.circuit.devices_dict.keys())[:]
            if not devices_to_check:
                devices_to_check = ["M1", "M2"] # Fallback

            # devices_to_check.extend(["PM1","PM25","PM7","PM9"])

            print(f"\n[部分器件详情 (示例)]")
            for name in devices_to_check:
                dev = analyzer.circuit.devices_dict.get(name)
                if dev:
                    # 将 Tags 转换为中文描述以便阅读
                    cn_tags = [AC.get_chinese_name(t) for t in dev.tags]
                    # 获取子结构引用信息
                    subs = [f"{AC.get_chinese_name(s.sub_type)}({s.sub_id})" for s in dev.substructures]
                    
                    print(f"  器件 {name}:")
                    print(f"    类型: {dev.type}")
                    print(f"    标签: {cn_tags}")
                    print(f"    所属子结构: {subs}")
                else:
                    print(f"  器件 {name}: 未找到")

            # --- 3. 检查拓扑识别结果 (映射新架构存储) ---
            print(f"\n[关键拓扑结构识别 (Tags & Groups)]")
            
            # # 辅助函数: 打印 Device Groups (对应原 diff_pair, output_pair 等列表)
            # def print_group(label, key):
            #     groups = analyzer.device_groups.get(key, [])
            #     if groups:
            #         print(f"  {label}: {groups}")
            #     else:
            #         print(f"  {label}: (无)")

            # # 辅助函数: 打印 Tag Index (对应原 diff_pair_positive 等集合)
            # def print_tag(label, key):
            #     names = analyzer.get_names_by_tag(key)
            #     if names:
            #         print(f"  {label}: {list(names)}")

            # # 辅助函数: 打印 Relation (对应原 cascode_cache 等字典)
            # def print_relation(label, rel_key):
            #     res = []
            #     for src, rels in analyzer.relation_graph.items():
            #         if rel_key in rels:
            #             targets = rels[rel_key]
            #             res.append(f"{src}->{targets}")
            #     if res:
            #         print(f"  {label}: {res}")
            #     else:
            #         print(f"  {label}: (无)")

            # # > 输入级
            # print_tag("差分正输入管", AC.TAG_DIFF_POS)
            # print_tag("差分负输入管", AC.TAG_DIFF_NEG)
            # print_group("差分输入对", AC.STR_DIFF_PAIR)
            # print("")
            
            # # > 输出级
            # print_tag("正端输出管", AC.TAG_OUTPORT_POS)
            # print_tag("负端输出管", AC.TAG_OUTPORT_NEG)
            # print_group("输出端对", AC.STR_OUTPORT_PAIR)
            # print_group("逻辑输出对", AC.STR_OUTPUT_PAIR)
            # print("")
            
            # # > 级联与电流镜 (核心关系)
            # print_relation("级联关系 (Main->Slave)", AC.REL_CASCODE_M2S)
            # print_relation("普通电流镜 (Ref->Mirror)", AC.REL_STD_REF2MIRROR)
            # print_relation("根偏置锁定 (Root->Bias)", AC.REL_STD_ROOT2BIAS)
            # print_relation("低压电流镜 (LRef->Token)", AC.REL_LV_LREF2TOKEN)
            # print("")
            
            # # > 无源与共模
            # print_group("频率补偿", AC.STR_FREQ_COMPENSATE)
            # print_group("共模检测(2管)", AC.STR_CM_DETECT_A)
            # print_group("共模检测(4管)", AC.STR_CM_DETECT_B)
            # print_group("对称电容", AC.STR_SYM_CAPACITOR)
            # print("")
            
            # # > 负载结构
            # print_group("A型负载", AC.STR_LOAD_A)
            # print_group("B型负载", AC.STR_LOAD_B)
            # print_group("典型负载", AC.STR_LOAD_TYPICAL)
            # print_group("低压镜像对", AC.STR_LV_MIRROR_PAIR)

            # # --- 4. 检查电流束内部网络 ---
            # print(f"\n[电流束内部网络 (Beam Net Sets)]")
            # if analyzer.circuit.beam_net_sets:
            #     for beam_id, net_set in analyzer.circuit.beam_net_sets.items():
            #         print(f"  {beam_id}: {list(net_set)}")
            # else:
            #     print("  (未生成)")

            # # --- 5. 检查电流路径 ---
            # print("\n[电流路径 (前10条)]")
            # if analyzer.circuit.current_paths:
            #     for i, path in enumerate(analyzer.circuit.current_paths[:10], 1):
            #         print(f"  路径{i}: {' -> '.join(path)}")
            #     if len(analyzer.circuit.current_paths) > 10:
            #         print(f"  ... (共 {len(analyzer.circuit.current_paths)} 条)")
            # else:
            #     print("  (未生成)")

            # # --- 6. 检查电流束概况 ---
            # print("\n[电流束 (Current Beams)]")
            # if analyzer.circuit.current_beams:
            #     for beam_id, paths in analyzer.circuit.current_beams.items():
            #         print(f"  {beam_id}: 聚合了 {len(paths)} 条路径")
            # else:
            #     print("  (未分析出电流束)")

            # # --- 7. 检查电流束具体路径 (抽象化) ---
            # print("\n[电流束路径 (Beam Paths - Abstract)]")
            # if analyzer.circuit.current_beam_paths:
            #     for beam_id, beam_path in analyzer.circuit.current_beam_paths.items():
            #         # beam_path 是 List[Set[str]]，将其格式化为 {M1,M2}->{M3,M4} 形式
            #         path_str = " -> ".join([
            #             f"{{{','.join(s)}}}" if len(s) > 1 else list(s)[0] if len(s) == 1 else "{}"
            #             for s in beam_path
            #         ])
            #         print(f"  {beam_id}:\n    {path_str}")
            # else:
            #     print("  (未生成)")

            # # --- 8. 检查登记的子结构实例 ---
            # print("\n[登记的子结构实例 (Substructures)]")
            # if analyzer.circuit.substructures:
            #     for i, sub in enumerate(analyzer.circuit.substructures, 1):
            #         cn_type = AC.get_chinese_name(sub.type)
            #         print(f"  实例 {i}: [{cn_type}] ID={sub.sub_id}")
            #         print(f"    成员: {sub.members}")
            #         # print(f"    约束: {sub.constraints}") # 调试时可开启
            # else:
            #     print("  (未登记任何子结构)")

            # # --- 9. 检查参数约束组 ---
            # print("\n[全局约束组 (Constraint Groups)]")
            # if analyzer.constraint_groups:
            #     print(f"  共生成 {len(analyzer.constraint_groups)} 个参数关联组：")
            #     # 仅打印前 5 组作为示例，防止刷屏
            #     for i, group in enumerate(analyzer.constraint_groups[:5], 1):
            #         print(f"  组 {i}: {group}")
            #     if len(analyzer.constraint_groups) > 5:
            #         print(f"  ... (剩余 {len(analyzer.constraint_groups)-5} 组未显示)")
            # else:
            #     print("  (未生成)")

            # # report = analyzer.calibrate_params
            # # print(report)

            print("\n" + "=" * 28 + " 测试输出结束 " + "=" * 28)

        except Exception as e:
            traceback.print_exc()
            print(f"\n[严重错误] 分析器运行失败: {e}")
    