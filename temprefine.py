import os
import copy
import traceback
import pyAether as ae
import itertools
import re
import math
from typing import Dict, List, Callable, Set, Optional, DefaultDict, Tuple
from collections import defaultdict
from parameter_manager import ParameterManager

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
    DeviceTags和SubStructureType是这个分析器的工具，代表这个分析器可以识别的器件标签和子结构类型。
    Device是该分析器识别到的器件、DeviceSub是器件所属子结构实例的引用
    Circuit是该分析器识别到的电路、CircuitSub是在Circuit中识别出的子结构实例
    子结构要先注册到SubStructureType中，才能被识别并登记到CircuitSub中与DeviceSub中
    """
    # ------------------------------
    # 1. 内部类定义
    # ------------------------------
    class DeviceTags:       #器件标签类，用于给器件打标签，使用方法为Device.tags.add(DeviceTags.DIODE_MOS)
        DIODE_MOS = "二极管连接MOS管"
        # ---------------------级联----------------------
        CASCODE_MAIN = "主级联"
        CASCODE_SLAVE = "从级联"
        # -------------------对称对----------------------
        DIFF_POSITIVE = "正端输入管"
        DIFF_NEGATIVE = "负端输入管"

        SYM_PAIR = "栅极对称管"  # 栅极接到对称电流支路的管子（输出对符合定义，但被优先识别，所以不会被识别成这个）

        OUTPUT_POSITIVE = "正端输出管"
        OUTPUT_NEGATIVE = "负端输出管"
        # --------------------电流镜----------------------
        LV_MIRROR_UPPER_REF = "上层参考管"
        LV_MIRROR_UPPER_BIAS = "上层偏置管"  # 上层参考管的偏置二极管，低压电流镜不一定有这个管子
        LV_MIRROR_LOWER_REF = "下层参考管"
        LV_MIRROR_UPPER_MIRROR = "上层镜像管"
        LV_MIRROR_LOWER_MIRROR = "下层镜像管"
        LV_MIRROR_BIAS_MIRROR = "偏置镜像管"
        LV_MIRROR_PAIR = "镜像对管"

        CURRENT_MIRROR_REF = "电流镜参考管"
        CURRENT_MIRROR_MIRROR = "电流镜镜像管"
        CURRENT_MIRROR_BIAS_MIRROR = "电流镜偏置镜像管"
        ROOT_REF = "根参考管"  # 处在电流源路径中

        IN_CURRENT_BEAM = "处在电流束"  # 用来判断是否为偏置管，偏置管即处在偏置电路中的管子
        # ----------------------负载------------------------
        SPEC_A_LOAD_DIO = "A型二极管负载"
        SPEC_A_LOAD_TYP = "A型典型负载"  # 有源电流镜负载

        SPEC_B_LOAD = "B型负载"  # 双二极管

        TYPICAL_LOAD = "典型负载"
        # ----------------共模检测----------------------
        COMMON_DETECT_A = "RC共模检测"

        COMMON_GET = "共模输入管"
        COMMON_OUT = "共模输出管"
        COMMON_DETECT_B = "4管共模检测"
        # ----------------------RC频率补偿-----------------------
        COMPENSATE = "频率补偿"
        # --------------------------滤波--------------------------
        SYM_CAPACITOR = "对称电容"      #一般指滤波电容

    class SubStructureType:
        """代表分析器可以识别的子结构"""

        def __init__(self, type_name: str, required_tags: Set[str],
                     constraint_rules: Callable[[List['CircuitAnalyzer.Device']], List[str]],
                     aggregation_rule: Callable):
            self.type_name = type_name      #子结构名称，str，默认使用中文
            self.required_tags = required_tags        #子结构所包含的器件应该具有的标签，Set[str]
            self.constraint_rules = constraint_rules    #子结构中器件间的参数约束，输入为Device类List，输出为约束字符串List
            self.aggregation_rule = aggregation_rule    #获取并判断一组器件是否属于该子结构，是则登记

    class DeviceSub:
        """用于设定器件Device所属子结构实例"""

        def __init__(self, sub_type: str, sub_id: str):
            self.sub_type = sub_type
            self.sub_id = sub_id

    class CircuitSub:
        """用于设定电路Circuit子结构实例"""

        def __init__(self, sub_id: str, type: str, members: List[str], constraints: List[str]):
            self.sub_id = sub_id
            self.type = type
            self.members = members
            self.constraints = constraints

    class Device:
        """用于存储分析器识别到的器件"""

        def __init__(self, name: str, type: str, terminals: Dict[str, str], params: Dict[str, str],
                     tags: Set[str] = None,
                     substructures: List['CircuitAnalyzer.DeviceSub'] = None):
            self.name = name    #器件名称
            self.type = type    #器件类型
            self.terminals = terminals      #器件端口字典
            self.params = params    #器件参数字典
            self.tags = set() if tags is None else tags     #器件标签集合
            self.substructures = [] if substructures is None else substructures     #器件所有所属子结构

    class Circuit:
        """用于存储分析器识别到的电路"""

        def __init__(self, devices_dict: Dict[str, 'CircuitAnalyzer.Device'] = None,
                     substructure_types: Dict[str, 'CircuitAnalyzer.SubStructureType'] = None,  #这里需要重构到分析器中
                     substructures: List['CircuitAnalyzer.CircuitSub'] = None,
                     current_paths: List[List[str]] = None,
                     current_beams: Dict[str, List[List[str]]] = None,
                     current_beam_paths: Dict[str, List[Set[str]]] = None,
                     beam_net_sets: Dict[str, Set[str]] = None
                     ):
            self.devices_dict = {} if devices_dict is None else devices_dict   #包含电路中所有的器件
            self.substructure_types = {} if substructure_types is None else substructure_types  #注册的子结构（可使用的子结构）
            self.substructures = [] if substructures is None else substructures     #登记的子结构（电路中实际存在的子结构）
            self.current_paths = [] if current_paths is None else current_paths  # 电流路径
            self.current_beams = {} if current_beams is None else current_beams  # 电流束
            self.current_beam_paths = {} if current_beam_paths is None else current_beam_paths  # 电流束路径
            self.beam_net_sets = {} if beam_net_sets is None else beam_net_sets  # 电流束网络

    # ------------------------------
    # 2. CircuitAnalyzer 类属性
    # ------------------------------

    # 定义默认集合常量,集中维护,便于修改
    _DEFAULT_POWER_POSITIVE = {"VDD", "AVDD", "VDDA", "VDD_CORE", "VCC"}
    _DEFAULT_POWER_NEGATIVE = {"VSS", "AVSS", "VSSA", "GND", "VEE", "GNDA", "gnd!"}
    _DEFAULT_INPUT_NEGATIVE = {"VINN", "VIN1", "VIN_NEG", "INN", "VIN-"}
    _DEFAULT_INPUT_POSITIVE = {"VINP", "VIN2", "VIN_POS", "INP", "VIN+"}
    _DEFAULT_OUTPUT_NEGATIVE = {"VOUTN", "VOUT1", "VOUT_NEG", "OUTN", "VOUT-"}
    _DEFAULT_OUTPUT_POSITIVE = {"VOUTP", "VOUT2", "VOUT_POS", "OUTP", "VOUT+"}
    _DEFAULT_COMMON_SIGN = {"VCM", "VCOM"}
    _DEFAULT_CURRENT_SOURCE = {"IREF", "IIN"}

    # ------------------------------
    # 3. CircuitAnalyzer 核心方法
    # ------------------------------

    def __init__(
            self,
            lib: str,
            cell: str,
            view: str,
            param_manager: ParameterManager,
            # 保持Optional标注
            power_positive: Optional[Set[str]] = None,
            power_negative: Optional[Set[str]] = None,
            input_positive: Optional[Set[str]] = None,
            input_negative: Optional[Set[str]] = None,
            output_positive: Optional[Set[str]] = None,
            output_negative: Optional[Set[str]] = None,
            common_sign: Optional[Set[str]] = None,
            current_source: Optional[Set[str]] = None
    ):
        # ————————————————————————————————— 导线集合支持外部扩展(默认值+用户自定义)————————————————————————————————————————————————
        self.power_positive = (
                power_positive | self._DEFAULT_POWER_POSITIVE) if power_positive is not None else self._DEFAULT_POWER_POSITIVE
        self.power_negative = (
                power_negative | self._DEFAULT_POWER_NEGATIVE) if power_negative is not None else self._DEFAULT_POWER_NEGATIVE
        self.input_positive = (
                input_positive | self._DEFAULT_INPUT_POSITIVE) if input_positive is not None else self._DEFAULT_INPUT_POSITIVE
        self.input_negative = (
                input_negative | self._DEFAULT_INPUT_NEGATIVE) if input_negative is not None else self._DEFAULT_INPUT_NEGATIVE
        self.output_positive = (
                output_positive | self._DEFAULT_OUTPUT_POSITIVE) if output_positive is not None else self._DEFAULT_OUTPUT_POSITIVE
        self.output_negative = (
                output_negative | self._DEFAULT_OUTPUT_NEGATIVE) if output_negative is not None else self._DEFAULT_OUTPUT_NEGATIVE
        self.common_sign = (
                common_sign | self._DEFAULT_COMMON_SIGN) if common_sign is not None else self._DEFAULT_COMMON_SIGN
        self.current_source = (
                current_source | self._DEFAULT_CURRENT_SOURCE) if current_source is not None else self._DEFAULT_CURRENT_SOURCE

        # -----------------------------------BIOS,引入两字典------------------------------------
        self.circuit = self.Circuit()

        self.param_manager = param_manager
        self.device_types = copy.deepcopy(param_manager.device_types)
        self.device_params = copy.deepcopy(param_manager.device_params)

        self._cv = None  # Aether电路视图对象

        self.net_device_map: DefaultDict[str, List[str]] = defaultdict(list)  # 网络-器件映射,网络名小写

        self.copy_tube_r_raw_map: Dict[str, Tuple[str, float]] = {}  # 存储 (ref_dev_name, r_raw)
        # -------------------------------------BOOT，缓存初始化---------------------------------------
        self.diff_pair_negative: List[str] = []  # 临时存储差分管
        self.diff_pair_positive: List[str] = []
        self.diff_pair: List[str] = []  # 输入对名称

        self.common_get: List[str] = []  # 共模输入对名称
        self.common_detect_b: List[str] = []  # 4管共模检测名称

        self.positive_output: List[str] = []  # 临时存储输出管
        self.negative_output: List[str] = []
        self.output_pair: List[List[str]] = []  # 输出对名称
        self.vip_output_pair: List[str] = []    # 关键输出对名称

        self.compensate: List[str] = []  # 频率补偿器件名称
        self.common_detect_a: List[str] = []  # RC共模检测器件名称
        self.capacitor_pair: List[List[str]] = []  # 对称电容名称（滤波电容）

        self.cascode_cache: Dict[str, List[str]] = {}  # 级联，键为主级联管子名称，值为从级联管子名称

        self.current_cache: Dict[str, List[str]] = {}  # 普通电流镜，先生成，后会被低压电流镜删减。键为参考管名称，值为镜像管名称
        self.root_bias_mirror: Dict[str,List[str]] = {}   #根偏置镜像管(不同根参考管的根偏置镜像管之间的电流匹配没做)
        # 低压电流镜，键为下层管名称，值中第一个str代表偏置电压提供方式，第二个是上层参考管
        self.lv_current: Dict[str, List[str]] = {} #如果MOS偏置，第三个是偏置MOS管名称，如果不是，第三个是镜像管名称

        self.sym_pair: List[List[str]] = []     #对称对，栅极接对称支路的管子（输出对定义上符合，但不在这个缓存中）
        self.typ_load: List[List[str]] = []     #典型负载名称
        self.A_load: List[List[str]] = []       #有源电流镜负载名称
        self.B_load: List[List[str]] = []       #二极管负载名称

        self.top_nodes: List['CircuitAnalyzer.Device'] = []  # 顶层节点器件列表，指电路中连接在电源正端的器件，是电路中电流路径的起点
        self._flat_beam_cache: Optional[List[Set[str]]] = None  # 用于缓存压平的电流束路径，每个元素是一条电流束路径所包含的所有器件
        self.circuit.beam_net_sets = defaultdict(set)       #每个元素是一条电流束路径所包含的所有网络

        self.constraint_groups: List[List[str]] = []        #电路的参数组合，偏多，因为没考虑主电路电流匹配
        self.calibrate_params: Dict[str,Dict[str,str]] = {}     #更新后的device_params字典（初始解）

        self.input_tail: List[str] = []     #输入支路尾电流源
        self.output_tail: List[List[str]] = []    #输出支路电流源对
        self.common_tail: List[List[str]] = []    #输入输出公共尾电流源对

        # --------------------------------BIOS,打开对应原理图-------------------------------
        self._load_aether_circuit(lib, cell, view)
        # ------------------- BOOT，读取/生成器件连接导线/参数/建立网络-器件映射/创建Device实例--------------
        self._init_device_terminals()
        ae.dbCloseCV(self._cv)

        # -----------------------------------------子结构注册-----------------------------------------------
        self._register_substructure_types()

        # ----------------------------------------特殊器件检测---------------------------------------------
        self._mark_obvious_tags()  # 标记二极管器件、输入器件、顶层节点、共模检测器件
        self._mark_output_devices()  # 标记输出管与频率补偿和共模检测A
        self._mark_common_mode_detect_b()  # 标记共模检测B器件

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
        # 缓存真正输出对
        self._get_vip_pair()

        # 4. 登记 RC 子结构
        self._register_rc_structures()

        # 5. 登记对称电容
        self._register_sym_capacitors()
        #-----------------------------------------电路独立参数生成、修改初始解----------------------------------------------
        # 预保存复制管电流复制比例
        self._precompute_r_raw_map()
        # 生成全局约束组
        self._generate_constraint_groups()
        # 修改初始解
        self._calibrate_device_params()


    # -------路径换成绝对路径--------
    #这个函数没有被用到
    def _normalize_linux_path(self, path: str) -> str:
        if not path:
            raise ValueError("路径不能为空字符串")
        normalized_path = path.replace("\\", "/")
        return os.path.abspath(normalized_path) if not os.path.isabs(normalized_path) else normalized_path

    # -------------------BIOS-------------------------
    def _load_aether_circuit(self, lib: str, cell: str, view: str):
        """仅负责加载Aether电路视图"""
        try:
            ae.emyInitAether("-adv")
        except ae.AetherError as e:
            raise RuntimeError(
                "pyAether初始化失败！请检查：\n"
                "1. Aether库路径是否添加到LD_LIBRARY_PATH\n"
                f"   示例：export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/opt/aether/lib\n"
                f"原始错误：{str(e)}"
            ) from e

        try:
            # 使用规范化路径
            normalized_lib = self._normalize_linux_path(lib)
            self._cv = ae.dbOpenCV(
                lib=lib,
                cell=cell,
                view=view
            )
        except ae.AetherError as e:
            err_msg = str(e).lower()
            if "library not found" in err_msg:
                raise FileNotFoundError(f"库'{normalized_lib}'不存在（Linux路径区分大小写）") from e
            elif "cell not found" in err_msg:
                raise FileNotFoundError(f"单元'{cell}'不存在于库'{normalized_lib}'中") from e
            elif "view not found" in err_msg:
                raise FileNotFoundError(f"视图'{view}'不存在于单元'{cell}'中") from e
            else:
                raise RuntimeError(f"打开电路视图失败：{str(e)}") from e

    # ----------------------BOOT，读取器件连接导线、参数、建立网络-器件映射、创建Device实例--------------------------
    def _init_device_terminals(self):
        """
        从pyAether读取端子, 构建 net_device_map 和 Device 实例。
        包含二极管连接重复添加的修复。
        """
        if not self._cv:  # 健壮性检查
            raise RuntimeError("pyAether (self._cv) 未初始化。无法在Online模式下运行。")

        for device_name, device_type in self.device_types.items():
            device_inst = ae.dbFindInst(self._cv, device_name)
            if not device_inst:
                raise ValueError(f"器件'{device_name}'未在视图中找到（区分大小写）")

            terminals: Dict[str, str] = {}
            for term in device_inst.instTerms:
                term_name = str(term.name)
                net_name = str(term.net.name)
                if device_type in ["PMOS", "NMOS"] and term_name in ["G", "D", "S", "B"]:
                    terminals[term_name] = net_name
                elif device_type in ["Resistor", "Capacitor"] and term_name in ["PLUS", "MINUS"]:
                    terminals[term_name] = net_name

            # 构建网络-器件映射 (避免二极管连接导致的重复添加)
            unique_lower_nets = set(net.lower() for net in terminals.values())
            for net_lower in unique_lower_nets:
                self.net_device_map[net_lower].append(device_name)

            # 创建基础Device实例
            self.circuit.devices_dict[device_name] = self.Device(  # <--- (修改) 使用内部类
                name=device_name,
                type=device_type,
                terminals=terminals,
                params=self._get_valid_device_params(device_name, device_type)
            )

    # ------------------------------
    # 核心工具方法
    # ------------------------------
    # ---------------连接到特定导线检测---------------------
    def _net_matches(self, net_name: str, target_set: Set[str]) -> bool:
        """网络匹配：大小写不敏感"""
        if not net_name:
            return False
        target_lower = {s.lower() for s in target_set}
        return net_name.lower() in target_lower

    # ------------对称电容识别辅助函数-----------
    def _is_net_power(self, net: str) -> bool:
        """检查网络是否连接到正电源或负电源"""
        return self._net_matches(net,self.power_positive) or self._net_matches(net,self.power_negative)

    # ------------对称电容识别辅助函数-----------
    def _get_mos_on_net(self, net: str, exclude_devices: Set[str]) -> Set[str]:
        """获取指定网络上连接的所有MOS管 (宽松匹配)"""
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

    # ----------------获取器件除类型外可变参数，用于初始化----------------
    def _get_valid_device_params(self, device_name: str, device_type: str) -> Dict[str, str]:
        if device_name not in self.device_params:
            raise KeyError(f"器件'{device_name}'参数缺失（检查ParameterManager）")

        params = self.device_params[device_name].copy()
        params.pop("type", None)

        if device_type in ["PMOS", "NMOS"]:
            required = {"fw", "l", "m"}
            missing = required - set(params.keys())
            if missing:
                raise ValueError(f"MOS管'{device_name}'缺少参数：{missing}")
        return params

    # ------------------连接到电源正端检测--------------------
    def _is_top_node(self, device: 'CircuitAnalyzer.Device') -> bool:
        """判断器件是否为顶层节点(连接电源正端)"""
        if device.type == "PMOS":
            s_net = device.terminals.get("S")
            return s_net is not None and self._net_matches(s_net, self.power_positive)
        elif device.type == "NMOS":
            d_net = device.terminals.get("D")
            return d_net is not None and self._net_matches(d_net, self.power_positive)
        elif device.type == "Resistor":
            nets = list(device.terminals.values())
            return any(self._net_matches(net, self.power_positive) for net in nets)
        return False

    # ---------------------------------------------子结构约束函数与子结构注册------------------------------------------------------
    def _register_substructure_types(self):
        """注册子结构类型及约束规则"""
        def sym_pair_constraint(members: List['CircuitAnalyzer.Device']) -> List[str]:
            """对称对约束：差分输入对、输出对、共模检测对、对称对（栅极接对称电流支路）
            fw/l/m需相同
            """
            if len(members) != 2:
                return list("")

            base_constraints = [  # 正常约束
                f"{members[0].name}_fw = {members[1].name}_fw",
                f"{members[0].name}_l = {members[1].name}_l",
                f"{members[0].name}_m = {members[1].name}_m"
            ]
            return base_constraints

        def low_voltage_mirror_constraint(members: List['CircuitAnalyzer.Device']) -> List[str]:
            """
                所有管子的约束向下层参考管看齐，没考虑电阻
            """
            try:
                # 1. 查找关键器件
                # 上层参考管
                upper_ref = [d for d in members if self.DeviceTags.LV_MIRROR_UPPER_REF in d.tags][0]
                # 下层参考管
                lower_ref = [d for d in members if self.DeviceTags.LV_MIRROR_LOWER_REF in d.tags][0]

                # 查找所有镜像管
                upper_mirrors = [d for d in members if self.DeviceTags.LV_MIRROR_UPPER_MIRROR in d.tags]
                lower_mirrors = [d for d in members if self.DeviceTags.LV_MIRROR_LOWER_MIRROR in d.tags]

                constraints = []

                # 上层参考管 与 lower_ref 的 fw/l/m 必须相同
                constraints.extend([
                    f"{upper_ref.name}_fw = {lower_ref.name}_fw",
                    f"{upper_ref.name}_l = {lower_ref.name}_l",
                    f"{upper_ref.name}_m = {lower_ref.name}_m"
                ])

                # 上层镜像管的 l 必须与 lower_ref 相同 (fw/m可不同)
                for m in upper_mirrors:
                    base = [f"{m.name}_l = {lower_ref.name}_l"]
                    if self.DeviceTags.LV_MIRROR_BIAS_MIRROR in m.tags:
                        base.extend([f"{m.name}_m = {lower_ref.name}_m", f"{m.name}_fw = {lower_ref.name}_fw"])
                    constraints.extend(base)

                # 下层镜像管的 l 必须与 lower_ref 相同 (fw/m可不同)
                for m in lower_mirrors:
                    base = [f"{m.name}_l = {lower_ref.name}_l"]
                    if self.DeviceTags.LV_MIRROR_BIAS_MIRROR in m.tags:
                        base.extend([f"{m.name}_m = {lower_ref.name}_m", f"{m.name}_fw = {lower_ref.name}_fw"])
                    constraints.extend(base)

                return constraints

            except IndexError:
                # 查找器件失败
                return ["# 错误：低压电流镜成员不完整，无法生成约束"]

        def cascode_constraint(members: List['CircuitAnalyzer.Device']) -> List[str]:
            """级联约束：
            l/fw/m均相同
            """
            main = [d for d in members if self.DeviceTags.CASCODE_MAIN in d.tags][0]
            slaves = [d for d in members if self.DeviceTags.CASCODE_SLAVE in d.tags]
            constraints = []
            for s in slaves:
                base = [f"{s.name}_l = {main.name}_l", f"{s.name}_fw = {main.name}_fw", f"{s.name}_m = {main.name}_m"]
                constraints.extend(base)
            return constraints

        def load_constraint(members: List['CircuitAnalyzer.Device']) -> List[str]:
            """负载约束：A型负载、B型负载、典型负载（2器件与4器件负载）
            l/fw/m均相同
            """
            length = len(members)
            base_constraints = []

            if length > 0:  # 健壮性检查
                ref_name = members[length - 1].name
                for i in range(length - 1):
                    dev_name = members[i].name
                    base_constraints.extend([
                        f"{dev_name}_fw = {ref_name}_fw",
                        f"{dev_name}_l = {ref_name}_l",
                        f"{dev_name}_m = {ref_name}_m"
                    ])
            return base_constraints

        def current_mirror_constraint(members: List['CircuitAnalyzer.Device']) -> List[str]:
            """
            普通电流镜约束:
            - m/l 始终约束
            - Bias mirrors (有BIAS标签):
                - If Ref is ROOT_REF: fw 相互约束, 但独立于 Ref
                - If Ref is not ROOT_REF: fw 约束为等于 Ref.fw
            """
            try:
                ref = [d for d in members if self.DeviceTags.CURRENT_MIRROR_REF in d.tags][0]
            except IndexError:
                return ["# 错误：普通电流镜缺少参考管"]

            mirrors = [d for d in members if self.DeviceTags.CURRENT_MIRROR_MIRROR in d.tags]
            constraints = []

            is_ref_root = self.DeviceTags.ROOT_REF in ref.tags

            bias_mirror_names = []  # 用于 Root Ref 的 fw 相互约束

            for m in mirrors:
                is_bias_mirror = self.DeviceTags.CURRENT_MIRROR_BIAS_MIRROR in m.tags

                # 1. m/l 约束 (始终应用)
                base = [ f"{m.name}_l = {ref.name}_l"]

                # 2. fw 约束
                if is_bias_mirror:
                    if is_ref_root:
                        # (Case 1): Ref是Root. fw 独立于 ref.
                        bias_mirror_names.append(m.name)
                    else:
                        # (Case 3): Ref非Root. fw = ref.fw
                        base.extend([f"{m.name}_m = {ref.name}_m",f"{m.name}_fw = {ref.name}_fw"])

                constraints.extend(base)

            # 3. 添加 Case 1 (Root Ref) 的 fw 相互约束
            if is_ref_root and len(bias_mirror_names) > 1:
                first_m = bias_mirror_names[0]
                for other_m in bias_mirror_names[1:]:
                    constraints.extend([f"{other_m}_m = {first_m}_m",f"{other_m}_fw = {first_m}_fw"])

            return constraints

        def common_detect_b_constraint(members: List['CircuitAnalyzer.Device']) -> List[str]:
            """共模检测B约束：
            fw/l/m需相同
            """
            base_constraints = [  # 正常约束
                f"{members[0].name}_fw = {members[3].name}_fw",
                f"{members[0].name}_l = {members[3].name}_l",
                f"{members[0].name}_m = {members[3].name}_m",
                f"{members[1].name}_fw = {members[3].name}_fw",
                f"{members[1].name}_l = {members[3].name}_l",
                f"{members[1].name}_m = {members[3].name}_m",
                f"{members[2].name}_fw = {members[3].name}_fw",
                f"{members[2].name}_l = {members[3].name}_l",
                f"{members[2].name}_m = {members[3].name}_m"
            ]
            return base_constraints

        def _rc_constraint_helper(members: List['CircuitAnalyzer.Device']) -> List[str]:
            """
            辅助函数：约束所有 R 参数相同，所有 C 参数相同。
            (R 使用 segW/segL, C 使用 l)
            """
            constraints = []
            resistors = [d for d in members if d.type == "Resistor"]
            capacitors = [d for d in members if d.type == "Capacitor"]

            # 约束电阻 (segW, segL)
            if len(resistors) > 1:
                ref_res = resistors[0]
                ref_params = ref_res.params

                # 检查参考电阻是否具有这些参数
                has_segW = "segW" in ref_params
                has_segL = "segL" in ref_params

                for res in resistors[1:]:
                    if has_segW:
                        constraints.append(f"{res.name}_segW = {ref_res.name}_segW")
                    if has_segL:
                        constraints.append(f"{res.name}_segL = {ref_res.name}_segL")

            # 约束电容 (l)
            if len(capacitors) > 1:
                ref_cap = capacitors[0]

                # 检查参考电容是否具有 'l' 参数
                if "l" in ref_cap.params:
                    for cap in capacitors[1:]:
                        constraints.append(f"{cap.name}_l = {ref_cap.name}_l")

            return constraints

        def compensate_constraint(members: List['CircuitAnalyzer.Device']) -> List[str]:
            """频率补偿约束 (R同, C同)"""
            return _rc_constraint_helper(members)

        def common_detect_a_constraint(members: List['CircuitAnalyzer.Device']) -> List[str]:
            """共模检测A约束 (R同, C同)"""
            return _rc_constraint_helper(members)

        def sym_capacitor_constraint(members: List['CircuitAnalyzer.Device']) -> List[str]:
            """对称电容约束 (l同)"""
            constraints = []
            capacitors = [d for d in members if d.type == "Capacitor"]

            if len(capacitors) > 1:
                ref_cap = capacitors[0]
                # 检查参考电容是否具有 'l' 参数
                if "l" in ref_cap.params:
                    for cap in capacitors[1:]:
                        constraints.append(f"{cap.name}_l = {ref_cap.name}_l")
            return constraints

        # ---------------------------------------子结构注册---------------------------------------------
        #--------------------------------------能识别出的子结构类型---------------------------------------
        self.circuit.substructure_types = {
            "差分输入对": self.SubStructureType(
                type_name="差分输入对",
                required_tags={self.DeviceTags.DIFF_POSITIVE, self.DeviceTags.DIFF_NEGATIVE},
                constraint_rules=sym_pair_constraint,
                aggregation_rule=lambda roles: lambda
                    roles: self.DeviceTags.DIFF_POSITIVE in roles and self.DeviceTags.DIFF_NEGATIVE in roles
            ),
            "输出对": self.SubStructureType(
                type_name="输出对",
                required_tags={self.DeviceTags.OUTPUT_NEGATIVE, self.DeviceTags.OUTPUT_POSITIVE},
                constraint_rules=sym_pair_constraint,
                aggregation_rule=lambda roles: lambda
                    roles: self.DeviceTags.OUTPUT_NEGATIVE and self.DeviceTags.OUTPUT_POSITIVE in roles
            ),
            "对称对": self.SubStructureType(
                type_name="对称对",
                required_tags={self.DeviceTags.SYM_PAIR, self.DeviceTags.COMMON_GET, self.DeviceTags.LV_MIRROR_PAIR},
                constraint_rules=sym_pair_constraint,
                aggregation_rule=lambda roles: lambda
                    roles: self.DeviceTags.SYM_PAIR or self.DeviceTags.COMMON_GET
                           or self.DeviceTags.LV_MIRROR_PAIR in roles
            ),
            "低压电流镜": self.SubStructureType(
                type_name="低压电流镜",
                required_tags={
                    self.DeviceTags.LV_MIRROR_LOWER_REF,
                    self.DeviceTags.LV_MIRROR_LOWER_MIRROR,
                    self.DeviceTags.LV_MIRROR_UPPER_MIRROR,
                    self.DeviceTags.LV_MIRROR_UPPER_REF
                },
                constraint_rules=low_voltage_mirror_constraint,
                aggregation_rule=lambda roles: all(r in roles for r in [
                    self.DeviceTags.LV_MIRROR_LOWER_REF,
                    self.DeviceTags.LV_MIRROR_LOWER_MIRROR,
                    self.DeviceTags.LV_MIRROR_UPPER_MIRROR,
                    self.DeviceTags.LV_MIRROR_UPPER_REF
                ])
            ),
            "级联": self.SubStructureType(
                type_name="级联",
                required_tags={self.DeviceTags.CASCODE_MAIN, self.DeviceTags.CASCODE_SLAVE},
                constraint_rules=cascode_constraint,
                aggregation_rule=lambda
                    roles: self.DeviceTags.CASCODE_MAIN in roles and self.DeviceTags.CASCODE_SLAVE in roles
            ),
            "普通电流镜": self.SubStructureType(
                type_name="普通电流镜",
                required_tags={self.DeviceTags.CURRENT_MIRROR_REF, self.DeviceTags.CURRENT_MIRROR_MIRROR},
                constraint_rules=current_mirror_constraint,
                aggregation_rule=lambda
                    roles: self.DeviceTags.CURRENT_MIRROR_REF in roles and self.DeviceTags.CURRENT_MIRROR_MIRROR in roles
            ),
            "A型负载": self.SubStructureType(
                type_name="A型负载",
                required_tags={self.DeviceTags.SPEC_A_LOAD_DIO, self.DeviceTags.SPEC_A_LOAD_TYP},
                constraint_rules=load_constraint,
                aggregation_rule=lambda
                    roles: self.DeviceTags.SPEC_A_LOAD_TYP and self.DeviceTags.SPEC_A_LOAD_DIO in roles
            ),
            "B型负载": self.SubStructureType(
                type_name="B型负载",
                required_tags={self.DeviceTags.SPEC_B_LOAD},
                constraint_rules=load_constraint,
                aggregation_rule=lambda roles: self.DeviceTags.SPEC_B_LOAD in roles
            ),
            "典型负载": self.SubStructureType(
                type_name="典型负载",
                required_tags={self.DeviceTags.TYPICAL_LOAD},
                constraint_rules=load_constraint,
                aggregation_rule=lambda roles: self.DeviceTags.TYPICAL_LOAD in roles
            ),
            "共模检测B": self.SubStructureType(
                type_name="共模检测B",
                required_tags={self.DeviceTags.COMMON_OUT, self.DeviceTags.COMMON_GET},
                constraint_rules=common_detect_b_constraint,
                aggregation_rule=lambda roles: self.DeviceTags.COMMON_OUT and self.DeviceTags.COMMON_GET in roles
            ),
            "频率补偿": self.SubStructureType(
                type_name="频率补偿",
                required_tags={self.DeviceTags.COMPENSATE},
                constraint_rules=compensate_constraint,
                aggregation_rule=lambda roles: self.DeviceTags.COMPENSATE in roles
            ),
            "共模检测A": self.SubStructureType(
                type_name="共模检测A",
                required_tags={self.DeviceTags.COMMON_DETECT_A},
                constraint_rules=common_detect_a_constraint,
                aggregation_rule=lambda roles: self.DeviceTags.COMMON_DETECT_A in roles
            ),
            "对称电容": self.SubStructureType(
                type_name="对称电容",
                required_tags={self.DeviceTags.SYM_CAPACITOR},
                constraint_rules=sym_capacitor_constraint,
                aggregation_rule=lambda roles: self.DeviceTags.SYM_CAPACITOR in roles
            )
        }

    # -------------------------------------------------------特殊器件检测------------------------------------------------------------
    def _mark_obvious_tags(self):
        for device in self.circuit.devices_dict.values():
            # ---------------------检测二极管连接MOS管------------------
            if device.type in ["PMOS", "NMOS"]:
                g_net = device.terminals.get("G")
                d_net = device.terminals.get("D")
                if g_net and d_net and self._net_matches(g_net, {d_net}):
                    device.tags.add(self.DeviceTags.DIODE_MOS)

            # -----------------------识别顶层节点-------------------------
            if self._is_top_node(device):
                self.top_nodes.append(device)

            # ------------------------标记差分输入管--------------------------
            if device.type in ["PMOS", "NMOS"]:
                g_net = device.terminals.get("G")
                if g_net:
                    if self._net_matches(g_net, self.input_positive):
                        device.tags.add(self.DeviceTags.DIFF_POSITIVE)
                        self.diff_pair_positive.append(device.name)
                    elif self._net_matches(g_net, self.input_negative):
                        device.tags.add(self.DeviceTags.DIFF_NEGATIVE)
                        self.diff_pair_negative.append(device.name)

            # ---------------------------------标记共模检测管---------------------------------
            if device.type in ["PMOS", "NMOS"]:
                g_net = device.terminals.get("G")
                if self._net_matches(g_net, self.common_sign):
                    device.tags.add(self.DeviceTags.COMMON_GET)
                    self.common_get.append(device.name)

    # ------------------------------------------------ 标记输出管/频率补偿/共模检测A --------------------------------------------------------
    def _mark_output_devices(self):
        """
        使用 net_device_map 快速标记输出管 (MOS)，
        根据预定义逻辑检测连接到输出端的 RC 结构，应用时应检查预定义逻辑是否匹配电路设计。
        """
        # --- 辅助函数 1: 获取二端器件的另一端网络(在电流路径中存在重合函数，可以优化) ---
        def _get_other_terminal_net(device: 'CircuitAnalyzer.Device', connected_net: str) -> Optional[str]:
            """获取电容/电阻的另一端网络名"""
            net1 = device.terminals.get("PLUS")
            net2 = device.terminals.get("MINUS")
            if not net1 or not net2:
                return None

            if self._net_matches(net1, {connected_net}):
                return net2
            elif self._net_matches(net2, {connected_net}):
                return net1
            return None

        # --- 辅助函数 2: 获取网络上的MOS连接 (宽松匹配) ---
        def _get_net_mos_connections(net: str, exclude_devices: Set[str]) -> List[Dict]:
            """
            获取指定网络上所有MOS管的连接信息。
            只关心MOS管，忽略其他器件。
            """
            if not net:
                return []

            mos_connections = []
            device_names_on_net = self.net_device_map.get(net.lower(), [])

            for dev_name in device_names_on_net:
                if dev_name in exclude_devices:
                    continue

                dev = self.circuit.devices_dict.get(dev_name)
                if not dev or dev.type not in ["PMOS", "NMOS"]:
                    continue

                # 判断连接类型
                if self._net_matches(dev.terminals.get("G"), {net}):
                    mos_connections.append({'conn_type': 'G', 'device': dev})
                else:
                    # 假设 S 或 D 连接
                    mos_connections.append({'conn_type': 'DS', 'device': dev})

            return mos_connections

        # --- 辅助函数 3: 检查网络是否只有单个电阻 ---
        def _get_net_single_resistor(net: str, exclude_devices: Set[str]) -> Optional['CircuitAnalyzer.Device']:
            """
            检查指定网络上是否 *仅* 包含一个电阻 (且无其他器件)。
            """
            if not net:
                return None

            devices_on_net = []
            device_names_on_net = self.net_device_map.get(net.lower(), [])

            for dev_name in device_names_on_net:
                if dev_name in exclude_devices:
                    continue
                dev = self.circuit.devices_dict.get(dev_name)
                if dev:
                    devices_on_net.append(dev)

            # 严格检查：网络上除排除列表外，必须只有1个器件，且它必须是电阻
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
                if not device:
                    continue

                # --- 规则 0: 标记 MOS 输出管 ---
                if device.type in ["PMOS", "NMOS"]:
                    if net_name.lower() in positive_nets_lower:
                        if self.DeviceTags.OUTPUT_POSITIVE not in device.tags and (
                                self._net_matches(device.terminals.get("S"), {net_name}) or self._net_matches(
                            device.terminals.get("D"), {net_name})):
                            device.tags.add(self.DeviceTags.OUTPUT_POSITIVE)
                            self.positive_output.append(dev_name)
                    elif net_name.lower() in negative_nets_lower:
                        if self.DeviceTags.OUTPUT_NEGATIVE not in device.tags and (
                                self._net_matches(device.terminals.get("S"), {net_name}) or self._net_matches(
                            device.terminals.get("D"), {net_name})):
                            device.tags.add(self.DeviceTags.OUTPUT_NEGATIVE)
                            self.negative_output.append(dev_name)

                # --- 规则 1: 器件是电容 ---
                elif device.type == "Capacitor":
                    cap_device = device
                    other_net = _get_other_terminal_net(cap_device, net_name)  # 输出端网络的另一端
                    if not other_net:
                        continue

                    exclude_set = {cap_device.name}
                    mos_conns = _get_net_mos_connections(other_net, exclude_set)
                    num_mos = len(mos_conns)

                    if num_mos > 1:
                        # Case C1 (多MOS): 标记 COMPENSATE
                        cap_device.tags.add(self.DeviceTags.COMPENSATE)
                        self.compensate.append(cap_device.name)

                    elif num_mos == 1:
                        if mos_conns[0]['conn_type'] == 'G':
                            # Case C2.1 (单MOS 栅极): 标记 COMMON_DETECT_A
                            cap_device.tags.add(self.DeviceTags.COMMON_DETECT_A)
                            self.common_detect_a.append(cap_device.name)
                        else:
                            # Case C2.2 (单MOS S/D): 标记 COMPENSATE
                            cap_device.tags.add(self.DeviceTags.COMPENSATE)
                            self.compensate.append(cap_device.name)

                    elif num_mos == 0:
                        # Case C3 (无MOS, 检查串联电阻)
                        serial_res = _get_net_single_resistor(other_net, exclude_set)
                        if serial_res:
                            # 确实是 C -> R 结构
                            far_net = _get_other_terminal_net(serial_res, other_net)  # 电阻未与电容相连的那一端
                            if not far_net:
                                continue

                            exclude_set_far = {cap_device.name, serial_res.name}
                            mos_conns_far = _get_net_mos_connections(far_net, exclude_set_far)
                            num_mos_far = len(mos_conns_far)

                            if num_mos_far > 1:
                                # Case C3.1 (C->R->多MOS): 标记 COMPENSATE
                                cap_device.tags.add(self.DeviceTags.COMPENSATE)
                                serial_res.tags.add(self.DeviceTags.COMPENSATE)
                                self.compensate.append(cap_device.name)
                                self.compensate.append(serial_res.name)

                            elif num_mos_far == 1:
                                if mos_conns_far[0]['conn_type'] == 'G':
                                    # Case C3.2.1 (C->R->单MOS 栅极): 跳过
                                    pass
                                else:
                                    # Case C3.2.2 (C->R->单MOS S/D): 标记 COMPENSATE
                                    cap_device.tags.add(self.DeviceTags.COMPENSATE)
                                    serial_res.tags.add(self.DeviceTags.COMPENSATE)
                                    self.compensate.append(cap_device.name)
                                    self.compensate.append(serial_res.name)
                        # else:
                        # Case C4 (无MOS, 也非单个电阻): 跳过

                # --- 规则 2: 器件是电阻 ---
                elif device.type == "Resistor":
                    res1_device = device
                    other_net = _get_other_terminal_net(res1_device, net_name)  # 未与输出端相连的那一端
                    if not other_net:
                        continue

                    exclude_set = {res1_device.name}
                    mos_conns = _get_net_mos_connections(other_net, exclude_set)
                    num_mos = len(mos_conns)

                    if num_mos > 1:
                        # Case R1 (多MOS): 跳过
                        pass

                    elif num_mos == 1:
                        if mos_conns[0]['conn_type'] == 'G':
                            # Case R2.1 (单MOS 栅极): 标记 COMMON_DETECT_A
                            res1_device.tags.add(self.DeviceTags.COMMON_DETECT_A)
                            self.common_detect_a.append(res1_device.name)
                        # else:
                        # Case R2.2 (单MOS S/D): 跳过

                    elif num_mos == 0:
                        # Case R3 (无MOS, 检查串联电阻)
                        serial_res2 = _get_net_single_resistor(other_net, exclude_set)
                        if serial_res2:
                            # 确实是 R1 -> R2 结构
                            far_net = _get_other_terminal_net(serial_res2, other_net)  # R2中未与R1电阻相连的那一端
                            if not far_net:
                                continue

                            exclude_set_far = {res1_device.name, serial_res2.name}
                            mos_conns_far = _get_net_mos_connections(far_net, exclude_set_far)
                            num_mos_far = len(mos_conns_far)

                            if num_mos_far == 1:
                                if mos_conns_far[0]['conn_type'] == 'G':
                                    # Case R3.2.1 (R1->R2->单MOS 栅极): 标记两者 COMMON_DETECT_A
                                    res1_device.tags.add(self.DeviceTags.COMMON_DETECT_A)
                                    serial_res2.tags.add(self.DeviceTags.COMMON_DETECT_A)
                                    self.common_detect_a.append(res1_device.name)
                                    self.common_detect_a.append(serial_res2.name)
                                # else:
                                # Case R3.1 (R1->R2->多MOS): 跳过
                                # Case R3.2.2 (R1->R2->单MOS S/D): 跳过
                        # else:
                        # Case R4 (无MOS, 也非单个电阻): 跳过

        # --- 主函数体 ---
        # 1. 处理正端输出
        positive_nets_lower = {n.lower() for n in self.output_positive}
        for net_name_lower in positive_nets_lower:
            device_names = self.net_device_map.get(net_name_lower, [])
            _process_output_net_devices(device_names, net_name_lower)

        # 2. 处理负端输出
        negative_nets_lower = {n.lower() for n in self.output_negative}
        for net_name_lower in negative_nets_lower:
            device_names = self.net_device_map.get(net_name_lower, [])
            _process_output_net_devices(device_names, net_name_lower)

    # ---------------------------------------------标记B型共模检测 ---------------------------------------------------
    ##################################################################################################################
    def _mark_common_mode_detect_b(self):
        """
        如果识别到2个共模输入管，则查找其共源极连接的另外两个MOS管。
        """
        if len(self.common_get) != 2:
            return

        try:
            dev1 = self.circuit.devices_dict[self.common_get[0]]
            dev2 = self.circuit.devices_dict[self.common_get[1]]

            s_net1 = dev1.terminals.get("S")
            s_net2 = dev2.terminals.get("S")
            # 检查源极是否连接到同一个网络
            if not s_net1 or s_net1 != s_net2:
                return
            common_s_net = s_net1
            # 查找连接到此共源极的所有器件
            all_devs_on_net = self.net_device_map.get(common_s_net.lower(), [])

            other_dev_names = [
                name for name in all_devs_on_net
                if name not in self.common_get
            ]
            other_mos_devices = []
            for name in other_dev_names:
                dev = self.circuit.devices_dict.get(name)
                if dev and dev.type in ["PMOS", "NMOS"] and self._net_matches(dev.terminals.get("S"), {common_s_net}):
                    other_mos_devices.append(dev)

            # 检查是否 *恰好* 连接另外两个MOS管
            if len(other_mos_devices) == 2:
                all_four_devices = [dev1, dev2] + other_mos_devices

                # 标记输出管
                other_mos_devices[0].tags.add(self.DeviceTags.COMMON_OUT)
                other_mos_devices[1].tags.add(self.DeviceTags.COMMON_OUT)
                self.common_detect_b = [dev1.name, dev2.name, other_mos_devices[0].name, other_mos_devices[1].name]
                # 标记整体结构
                for dev in all_four_devices:
                    dev.tags.add(self.DeviceTags.COMMON_DETECT_B)
                # print(f"信息：识别到B型共模检测结构，成员: {[d.name for d in all_four_devices]}")

        except KeyError:
            print("器件名称不在 self.circuit.devices_dict 中，忽略")
            pass

    ##########################################级联与普通电流镜标记#########################################################
    ##################################################################################################################
    def _analyze_diode_mos_structures(self):
        groups = self._find_slave_mos_and_form_groups()
        for group in groups:
            self._mark_cascode_roles(group)
            self._mark_current_mirror_roles(group)

    def _find_slave_mos_and_form_groups(self) -> List[Dict]:
        """
        查找所有二极管连接的MOS管(master)及其栅极连接的从MOS管(slaves)，
        """
        groups = []
        masters = [
            device for device in self.circuit.devices_dict.values()
            if self.DeviceTags.DIODE_MOS in device.tags
        ]

        for master in masters:
            g_net = master.terminals.get("G")
            if not g_net:
                continue

            slave_names = self.net_device_map.get(g_net.lower(), [])
            slaves = []
            for name in slave_names:
                if name == master.name:
                    continue

                device = self.circuit.devices_dict.get(name)

                if not device:
                    continue
                if device.type not in ["PMOS", "NMOS"]:
                    continue

                if self._net_matches(device.terminals.get("G"), {g_net}):
                    slaves.append(device)

            groups.append({"master": master, "slaves": slaves, "g_net": g_net})

        return groups

    def _mark_cascode_roles(self, group: Dict):
        master = group["master"]
        slaves = group["slaves"].copy()  # 实际是要对Device修改的，用浅copy是对的，深copy是错的
        current_s_net = master.terminals.get("S")
        cascode_slaves = []

        while slaves:
            found = next(
                (s for s in slaves if s.terminals.get("D") == current_s_net),
                None
            )
            if not found:
                break
            found.tags.add(self.DeviceTags.CASCODE_SLAVE)
            cascode_slaves.append(found)
            current_s_net = found.terminals.get("S")
            slaves.remove(found)

        if cascode_slaves:
            master.tags.add(self.DeviceTags.CASCODE_MAIN)
            slave_names = [s.name for s in cascode_slaves]
            self.cascode_cache[master.name] = slave_names
            # 还有一些别的子结构也可以在此阶段登记，而这里的登记也可以放到后面，没有统一登记只是懒得改而已
            self.aggregate_substructure("级联", [master] + cascode_slaves, f"cascode_{master.name}")

    def _mark_current_mirror_roles(self, group: Dict):
        master = group["master"]
        remaining_slaves = [s for s in group["slaves"] if self.DeviceTags.CASCODE_SLAVE not in s.tags]
        if not remaining_slaves:
            return
        master.tags.add(self.DeviceTags.CURRENT_MIRROR_REF)
        for slave in remaining_slaves:
            slave.tags.add(self.DeviceTags.CURRENT_MIRROR_MIRROR)

        mirror_names = [s.name for s in remaining_slaves]
        self.current_cache[master.name] = mirror_names

    ##################################################################################################################
    ##################################################################################################################
    # -----------------------------------------根参考管标记-------------------------------------------------
    def _mark_root_reference_path(self):
        """
        根据电流源端口(如IREF/IIN)查找“电流源路径”。
        并为该路径上所有器件(必须是二极管连接的电流镜参考管)打上ROOT_REF标签。
        """
        # 1. 查找起始网络
        start_net = None
        start_net_device_names = []

        # 使用 .lower() 匹配 net_device_map 的键
        current_source_lower = {s.lower() for s in self.current_source}

        for net_key in self.net_device_map.keys():
            if net_key in current_source_lower:
                start_net = net_key
                start_net_device_names = self.net_device_map[net_key]
                break  # 假设只有一个匹配的网络

        if not start_net:
            raise ValueError("信息：未找到电流源路径起始点 (IREF/IIN)，需扩展电流源网络名称或检查电路设计。")
            # return  # 未找到起始网络，正常退出

        # 2. 查找起始器件
        # 路径的起始点必须是唯一的二极管连接的参考管
        start_candidates = []
        for dev_name in start_net_device_names:
            dev = self.circuit.devices_dict.get(dev_name)
            if dev and (self.DeviceTags.DIODE_MOS in dev.tags and
                        self.DeviceTags.CURRENT_MIRROR_REF in dev.tags):
                start_candidates.append(dev)

        # 根据约束，这条路径的起点必须是唯一的
        if len(start_candidates) != 1:
            raise ValueError(f"警告：电流源网络 '{start_net}' 未找到或找到多个 (>=1) 根参考管。")

        current_device = start_candidates[0]

        # 3. 循环遍历路径，直到负电源
        while current_device:
            # 检查约束 (理论上已在查找时满足，但双重检查)
            if not (self.DeviceTags.DIODE_MOS in current_device.tags and
                    self.DeviceTags.CURRENT_MIRROR_REF in current_device.tags):
                break  # 路径中断，不满足约束

            # 标记为根参考管
            current_device.tags.add(self.DeviceTags.ROOT_REF)

            # 4. 根据类型查找下一个网络节点
            next_net = None
            if current_device.type == "NMOS":
                # NMOS 向下查找源极 S
                next_net = current_device.terminals.get("S")
            elif current_device.type == "PMOS":
                # PMOS 向下查找漏极 D
                next_net = current_device.terminals.get("D")
            else:
                raise ValueError(f"警告：电流源网络 '{start_net}' 只应该包含MOS管。")

            # 5. 检查是否到达终止条件 (电源负端)
            if not next_net or self._net_matches(next_net, self.power_negative):
                # print(f"信息：电流源路径在 {current_device.name} 处到达负电源。")
                break  # 路径结束

            # 6. 查找下一个器件
            next_net_device_names = self.net_device_map.get(next_net.lower(), [])

            candidates = []
            for dev_name in next_net_device_names:
                if dev_name == current_device.name:
                    continue  # 跳过自己

                dev = self.circuit.devices_dict.get(dev_name)
                # 路径上的下一个器件也必须是二极管连接的参考管
                if dev and (self.DeviceTags.DIODE_MOS in dev.tags and
                            self.DeviceTags.CURRENT_MIRROR_REF in dev.tags):
                    candidates.append(dev)

            # 路径必须是单向且唯一的
            if len(candidates) == 1:
                current_device = candidates[0]  # 找到了，继续循环
            else:
                raise ValueError(f"警告：电流源网络 '{start_net}' 存在至少{len(candidates)}条电流源路径。")

    #################################################低压电流镜标记######################################################
    ##################################################################################################################
    def _detect_low_voltage_current_mirrors(self):
        """检测低压电流镜"""
        mos_devices = [d for d in self.circuit.devices_dict.values() if d.type in ["PMOS", "NMOS"]]
        processed_mos = set()

        # 预构建栅极网络,MOS管映射
        gate_net_map: DefaultDict[str, Set['CircuitAnalyzer.Device']] = defaultdict(set)  #
        for mos in mos_devices:
            g_net = mos.terminals.get("G")
            if g_net:
                gate_net_map[g_net.lower()].add(mos)

        for a in mos_devices:
            a_name = a.name
            if a_name in processed_mos:
                continue

            a_g = a.terminals.get("G")
            a_d = a.terminals.get("D")
            a_s = a.terminals.get("S")
            if not (a_g and a_d and a_s):
                continue

            # 优化：通过网络映射快速查找潜在匹配的B管
            candidate_b_names = set()
            # 情况1相关管子:B的G连A的D,查找连接A的D网络的器件
            if a_d:
                candidate_b_names.update(self.net_device_map.get(a_d.lower(), []))
            # 情况2相关管子:B的D连A的G,查找连接A的G网络的器件
            if a_g:
                candidate_b_names.update(self.net_device_map.get(a_g.lower(), []))

            # 仅遍历候选B管,减少循环次数
            for b_name in candidate_b_names:
                if b_name == a_name or b_name in processed_mos:
                    continue
                b = self.circuit.devices_dict.get(b_name)
                if not b or b.type not in ["PMOS", "NMOS"]:
                    continue

                b_g = b.terminals.get("G")
                b_d = b.terminals.get("D")
                b_s = b.terminals.get("S")
                if not (b_g and b_d and b_s):
                    continue

                # 情况1：B的G连A的D，B的D连A的S
                if self._net_matches(b_g, {a_d}) and self._net_matches(b_d, {a_s}) and not self._net_matches(b_g,
                                                                                                             {a_g}):
                    a.tags.add(self.DeviceTags.LV_MIRROR_UPPER_REF)  #
                    b.tags.add(self.DeviceTags.LV_MIRROR_LOWER_REF)
                    processed_mos.add(a_name)
                    processed_mos.add(b_name)
                    self._mark_low_voltage_mirrors(a, b, gate_net_map)  # 传入预构建的映射
                    break

                # 情况2：B的D连A的G，B的S连A的D
                if self._net_matches(b_d, {a_g}) and self._net_matches(b_s, {a_d}) and not self._net_matches(b_g,
                                                                                                             {a_g}):
                    b.tags.add(self.DeviceTags.LV_MIRROR_UPPER_REF)  #
                    a.tags.add(self.DeviceTags.LV_MIRROR_LOWER_REF)
                    processed_mos.add(a_name)
                    processed_mos.add(b_name)
                    self._mark_low_voltage_mirrors(b, a, gate_net_map)  # 传入预构建的映射
                    break

    #################################################低压电流镜标记######################################################
    ##################################################################################################################
    def _mark_low_voltage_mirrors(self, upper_ref: 'CircuitAnalyzer.Device', lower_ref: 'CircuitAnalyzer.Device',
                                  gate_net_map):
        """标记低压电流镜的镜像管"""
        upper_ref_g = upper_ref.terminals["G"]
        lower_ref_g = lower_ref.terminals["G"]

        upper_bias = None
        upper_mirrors_list = []

        # 情况 (1): "耦合" 上层管是镜像管
        if self.DeviceTags.CURRENT_MIRROR_MIRROR in upper_ref.tags:  #
            # 查找与上层管在同一栅极的二极偏置管
            devices_on_gate = gate_net_map.get(upper_ref_g.lower(), set())
            diode_mos_list = [d for d in devices_on_gate if self.DeviceTags.DIODE_MOS in d.tags]  #

            if diode_mos_list:
                upper_bias = diode_mos_list[0]
                upper_bias.tags.add(self.DeviceTags.LV_MIRROR_UPPER_BIAS)  # 赋予偏置标签 #
            else:
                # 严重错误：上层参考管应该有偏置管，但没找到
                print(f"警告：LV结构 {upper_ref.name} 缺少二极管偏置管，无法登记。")
                return

        # 3. 标记上层镜像管 (基于upper_ref)
        all_upper_devices_on_gate = gate_net_map.get(upper_ref_g.lower(), set())

        for mos in all_upper_devices_on_gate:
            # 排除参考管与偏置二极管
            if mos.name == upper_bias.name or mos.name == upper_ref.name:
                continue

            mos.tags.add(self.DeviceTags.LV_MIRROR_UPPER_MIRROR)  #
            upper_mirrors_list.append(mos)

        # 4. 标记下层镜像管 (基于 lower_ref)
        all_lower_devices_on_gate = gate_net_map.get(lower_ref_g.lower(), set())
        lower_mirrors_list = []

        for mos in all_lower_devices_on_gate:
            if mos.name == lower_ref.name:
                continue

            mos.tags.add(self.DeviceTags.LV_MIRROR_LOWER_MIRROR)  #
            lower_mirrors_list.append(mos)

        if upper_mirrors_list and lower_mirrors_list:  # 上下都一定要有镜像管
            # 收集所有镜像管的名称
            all_mirror_names = [m.name for m in upper_mirrors_list] + \
                               [m.name for m in lower_mirrors_list]

            if upper_bias:  #
                # 检查这个耦合结构是否在普通电流镜缓存中
                if upper_bias.name in self.current_cache:
                    print(f"  [净化]: 检测到LV耦合，正在净化 {upper_bias.name} 及其普通电流镜...")

                    # 1. 获取所有被错误标记的镜像管
                    mirror_names_to_clean = self.current_cache[upper_bias.name]

                    # 2. (关键) 清除所有镜像管的陈旧标签
                    for name in mirror_names_to_clean:
                        if name in self.circuit.devices_dict:
                            self.circuit.devices_dict[name].tags.discard(self.DeviceTags.CURRENT_MIRROR_MIRROR)

                    # 3. (关键) 清除参考管的陈旧标签
                    upper_bias.tags.discard(self.DeviceTags.CURRENT_MIRROR_REF)

                    # 4. (关键) 清除缓存
                    del self.current_cache[upper_bias.name]

                # 构建值列表: [偏置指示字符串, 上层参考管, (二极偏置管), mirrors]
                value_list = ["MOS_BIAS"] + [upper_ref.name] + [upper_bias.name] + all_mirror_names
            else:
                # 电阻作偏置情况
                value_list = ["RES_BIAS"] + [upper_ref.name] + all_mirror_names

            self.lv_current[lower_ref.name] = value_list

    # -----------------------------------------------------电流路径生成-----------------------------------------------------------
    #: 确保路径包含网络 ---
    def generate_current_paths(self):
        """优化电阻基准网络计算，统一子节点与父节点的连接网络"""
        all_paths: List[List[str]] = []

        # ------------------------------
        # 通用辅助函数
        # ------------------------------
        def get_terminals(device: 'CircuitAnalyzer.Device') -> Dict[str, str]:  #
            """获取器件有效端子-网络映射（源漏/正负端）"""
            if device.type in ["PMOS", "NMOS"]:
                return {k: v for k, v in device.terminals.items() if k in ["S", "D"]}
            elif device.type == "Resistor":
                return {k: v for k, v in device.terminals.items() if k in ["PLUS", "MINUS"]}
            return {}

        def get_other_net(device: 'CircuitAnalyzer.Device', known_net: str) -> str:  #
            """获取器件中与已知网络不同的另一端网络"""
            nets = list(get_terminals(device).values())
            # 健壮性检查，防止 nets 列表为空或长度不足
            if len(nets) < 2:
                return ""
            return nets[0] if nets[1] == known_net else nets[1] if nets[0] == known_net else ""

        def get_res_other_net(device: 'CircuitAnalyzer.Device', target_set: Set[str]) -> str:  #
            """获取电阻非电源的一端网络"""
            if not device:
                return ""
            target_lower = {s.lower() for s in target_set}
            term_nets = list(get_terminals(device).values())
            if len(term_nets) < 2:
                return ""
            (net1, net2) = term_nets
            return net1 if net2.lower() in target_lower else net2 if net1.lower() in target_lower else ""

        # 子节点扩展核心逻辑（包含电阻基准网络）
        # ------------------------------
        def find_children(current: 'CircuitAnalyzer.Device', parent_net: str = None) -> List[
            'CircuitAnalyzer.Device']:  #
            current_type = current.type
            terminals = get_terminals(current)
            children: List['CircuitAnalyzer.Device'] = []  #

            if current_type == "NMOS":
                # 基准网络：NMOS的源极（S）
                s_net = terminals.get("S")
                if not s_net:
                    return []

                # 子节点：漏极接S的其他NMOS
                children.extend([
                    d for d in self.circuit.devices_dict.values()
                    if d.type == "NMOS" and d.name != current.name and d.terminals.get("D") == s_net
                ])

                # 子节点：一端接S且另一端符合条件的电阻（中间电阻）
                for res in [d for d in self.circuit.devices_dict.values() if
                            d.type == "Resistor" and d.name != current.name]:
                    res_nets = get_terminals(res).values()
                    if s_net not in res_nets:
                        continue
                    other_net = get_other_net(res, s_net)
                    if not other_net:
                        continue

                    valid = (self._net_matches(other_net, self.power_negative)) or any(
                        (d.type == "NMOS" and d.terminals.get("D") == other_net)
                        for d in self.circuit.devices_dict.values() if d.name != res.name
                    )
                    if valid:
                        children.append(res)

            elif current_type == "PMOS":
                # 基准网络：PMOS的漏极（D）
                d_net = terminals.get("D")
                if not d_net:
                    return []

                # 子节点：漏极接D的NMOS 或 源极接D的PMOS
                children.extend([
                    d for d in self.circuit.devices_dict.values()
                    if d.name != current.name and (
                            (d.type == "NMOS" and d.terminals.get("D") == d_net) or
                            (d.type == "PMOS" and d.terminals.get("S") == d_net)
                    )
                ])

                # 子节点：一端接D且另一端符合条件的电阻（中间电阻）
                for res in [d for d in self.circuit.devices_dict.values() if
                            d.type == "Resistor" and d.name != current.name]:
                    res_nets = get_terminals(res).values()
                    if d_net not in res_nets:
                        continue
                    other_net = get_other_net(res, d_net)
                    if not other_net:
                        continue

                    valid = (self._net_matches(other_net, self.power_negative)) or any(
                        (d.type == "NMOS" and d.terminals.get("D") == other_net) or
                        (d.type == "PMOS" and d.terminals.get("S") == other_net)
                        for d in self.circuit.devices_dict.values() if d.name != res.name
                    )
                    if valid:
                        children.append(res)

            elif current_type == "Resistor":
                # 确定电阻的基准网络（区分顶层/中间）
                if parent_net is not None and parent_net in get_terminals(current).values():
                    # 中间电阻：基准网络是与父节点连接端相对的另一端
                    base_net = get_other_net(current, parent_net)
                else:
                    # 顶层电阻
                    base_net = get_res_other_net(current, self.power_positive)

                if not base_net:  # <--- 健壮性检查
                    return []

                # 子节点：漏极接base_net的NMOS 或 源极接base_net的PMOS
                children.extend([
                    d for d in self.circuit.devices_dict.values()
                    if d.name != current.name and (
                            (d.type == "NMOS" and d.terminals.get("D") == base_net) or
                            (d.type == "PMOS" and d.terminals.get("S") == base_net)
                    )
                ])

            return children

        # ------------------------------
        # 路径终止判断
        # ------------------------------
        def _is_path_terminated(device: 'CircuitAnalyzer.Device') -> bool:  #
            """判断路径是否终止"""
            if device.type == "NMOS":
                return self._net_matches(device.terminals.get("S"), self.power_negative)
            elif device.type == "PMOS":
                # 这里其实存在逻辑冗余
                s_net = device.terminals.get("S")
                d_net = device.terminals.get("D")
                return self._net_matches(s_net, self.power_negative) or self._net_matches(d_net, self.power_negative)
            elif device.type == "Resistor":
                nets = list(device.terminals.values())
                return any(self._net_matches(net, self.power_negative) for net in nets)
            return False

        # ------------------------------
        # DFS函数（优化子节点与父节点的连接网络计算）
        # ------------------------------
        def dfs(current: 'CircuitAnalyzer.Device', path: List[str], parent_net: str = None):  #
            if current.name in path:
                return  # 避免同路径环路

            new_path = path + [current.name]
            if _is_path_terminated(current):
                all_paths.append(new_path)
                return

            # 计算当前节点的基准网络（所有子节点与当前节点的连接网络均为此网络）
            current_type = current.type
            current_terminals = get_terminals(current)
            # 父节点的基准网络：子节点与当前节点连接的网络（统一为当前节点的扩展基准）
            if current_type == "NMOS":
                child_parent_net = current_terminals.get("S")  # NMOS的扩展基准是S
            elif current_type == "PMOS":
                child_parent_net = current_terminals.get("D")  # PMOS的扩展基准是D
            elif current_type == "Resistor":
                # 电阻的扩展基准是其base_net（已在find_children中确定）
                # 子节点与电阻的连接网络即base_net
                if parent_net is not None:
                    child_parent_net = get_other_net(current, parent_net)  # 中间电阻的base_net
                else:
                    child_parent_net = get_res_other_net(current, self.power_positive)  # 顶层电阻的base_net
            else:
                child_parent_net = None

            # 健壮性检查
            if child_parent_net is None:
                return

            # 递归处理所有子节点，共享同一个child_parent_net
            for child in find_children(current, parent_net):
                # --- (修改) 将内部网络添加到路径中 ---
                dfs(child, new_path + [child_parent_net], child_parent_net)

        for node in self.top_nodes:
            dfs(node, [], parent_net=None)

        self.circuit.current_paths = all_paths

    # -----------------------------------------------------电流束生成、电流束路径生成、电流束管标记-----------------------------------------------------------
    def analyze_current_beams(self):
        """
        根据定义的规则获取电流束。
        必须在 generate_current_paths() 之后调用。
        使用 [Dev, Net, Dev] 格式，并提取内部网络集合。
        """
        # 0. 确保电流路径已生成
        if not self.circuit.current_paths:
            print("警告：电流路径未生成，请先调用 generate_current_paths()")

        # 复制一份路径列表，以便安全地从中移除
        # 使用元组的集合 (set of tuples) 来方便地进行 O(1) 查找和移除
        remaining_paths: Set[tuple] = {tuple(path) for path in self.circuit.current_paths}
        beams: Dict[str, List[List[str]]] = {}

        # -----------------------------------------------------
        # 规则 1: 所有包含差分输入管在内的电流路径
        # -----------------------------------------------------
        #
        beam1_devices = set(self.diff_pair_positive) | set(self.diff_pair_negative)
        beam1_paths: Set[tuple] = set()

        if beam1_devices:
            for path in remaining_paths:
                path_devs = path[::2]  # <--- (修改) 适配 [Dev, Net, Dev]
                if any(device_name in beam1_devices for device_name in path_devs):
                    beam1_paths.add(path)

        if beam1_paths:
            beams["beam_1_differential"] = [list(p) for p in beam1_paths]
            remaining_paths -= beam1_paths  # 从剩余路径中移除

        # -----------------------------------------------------
        # 规则 2: （剩余路径中）所有包含输出管的电流路径
        # -----------------------------------------------------
        #
        beam2_devices = set(self.positive_output) | set(self.negative_output)
        beam2_paths: Set[tuple] = set()

        if beam2_devices:
            for path in remaining_paths:
                path_devs = path[::2]  # <--- (修改) 适配 [Dev, Net, Dev]
                if any(device_name in beam2_devices for device_name in path_devs):
                    beam2_paths.add(path)

        if beam2_paths:
            beams["beam_2_output"] = [list(p) for p in beam2_paths]
            remaining_paths -= beam2_paths

        # -----------------------------------------------------
        # 规则 2.5: 共模检测B
        # -----------------------------------------------------
        #
        beamb_devices = self.common_detect_b
        beamb_paths: Set[tuple] = set()

        if beamb_devices:
            for path in remaining_paths:
                path_devs = path[::2]  # <--- (修改) 适配 [Dev, Net, Dev]
                if any(device_name in beamb_devices for device_name in path_devs):
                    beamb_paths.add(path)

        if beamb_paths:
            beams["beam_b_output"] = [list(p) for p in beamb_paths]
            remaining_paths -= beamb_paths

        # -----------------------------------------------------
        # 规则 3: （剩余路径中）所有包含输出管栅极对应的网络的、且包含器件数量相等的电流路径(这里逻辑或许可以优化)
        # -----------------------------------------------------
        # 3a. 找出所有输出管的栅极网络
        out_gate_nets: Set[str] = set()
        for dev_name in (self.positive_output + self.negative_output):
            device = self.circuit.devices_dict.get(dev_name)
            if device:
                g_net = device.terminals.get("G")
                if g_net:
                    out_gate_nets.add(g_net)

        # 3b. 【优化】利用 net_device_map 找出连接到这些网络的所有器件
        devices_on_out_g_nets: Set[str] = set()
        if out_gate_nets:
            for net in out_gate_nets:
                # 使用 .lower() 匹配 net_device_map 的键
                devices_on_out_g_nets.update(self.net_device_map.get(net.lower(), []))

        beam3_candidates: Set[tuple] = set()
        if devices_on_out_g_nets:
            # 3c. 找出剩余路径中，有哪些路径“包含”这些器件
            for path in remaining_paths:
                path_device_set = set(path[::2])  # <--- (修改) 适配 [Dev, Net, Dev]
                # 检查路径器件集合 与 目标器件集合 是否有交集
                if not path_device_set.isdisjoint(devices_on_out_g_nets):
                    beam3_candidates.add(path)

        # 3d. 将这些候选路径按长度分组
        grouped_by_length_beam3: DefaultDict[int, List[List[str]]] = defaultdict(list)
        for path in beam3_candidates:
            grouped_by_length_beam3[len(path[::2])].append(list(path))  # <--- (修改) 适配 [Dev, Net, Dev]

        # 3e. 将每个长度组作为一个电流束登记
        beam3_idx = 1
        paths_to_remove_for_beam3: Set[tuple] = set()
        for length, path_list in grouped_by_length_beam3.items():
            if len(path_list) > 1:  # 真正成束
                beams[f"beam_3_out_gate_len{length}_group{beam3_idx}"] = path_list
                # 记录这些路径，以便稍后从 remaining_paths 中移除
                paths_to_remove_for_beam3.update(tuple(p) for p in path_list)
                beam3_idx += 1

        remaining_paths -= paths_to_remove_for_beam3

        # -----------------------------------------------------
        # 规则 4: （剩余路径中）包含器件数量相等的、且有至少一个公共器件的电流路径
        # 公共器件的定义为：在两条路径中的位置索引一定分别相等。
        # -----------------------------------------------------
        # 4a. 按长度对所有剩余路径进行分组
        remaining_grouped_by_length: DefaultDict[int, List[tuple]] = defaultdict(list)
        for path_tuple in remaining_paths:
            remaining_grouped_by_length[len(path_tuple[::2])].append(path_tuple)  # <--- (修改) 适配 [Dev, Net, Dev]

        beam4_idx = 1
        paths_to_remove_for_beam4: Set[tuple] = set()

        for length, paths in remaining_grouped_by_length.items():
            if len(paths) <= 1:  # 至少需要2条路径才能形成“束”
                continue

            # 使用并查集（Disjoint Set Union）来查找连通分量
            # “连通”定义为：共享至少一个“同索引”的器件
            parent = list(range(len(paths)))  # DSU 数组

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

            # 4b. 遍历所有路径对，如果它们共享“同索引”器件，则合并
            for i in range(len(paths)):
                for j in range(i + 1, len(paths)):

                    path_i_devs = paths[i][::2]  # <--- (修改) 适配 [Dev, Net, Dev]
                    path_j_devs = paths[j][::2]  # <--- (修改) 适配 [Dev, Net, Dev]

                    has_common_indexed_device = False
                    for k in range(length):
                        if path_i_devs[k] == path_j_devs[k]:
                            has_common_indexed_device = True
                            break  # 找到一个即可

                    if has_common_indexed_device:
                        unite_sets(i, j)

            # 4c. 根据并查集的结果构建最终的束
            final_groups: DefaultDict[int, List[List[str]]] = defaultdict(list)
            for i in range(len(paths)):
                root = find_set(i)
                final_groups[root].append(list(paths[i]))  # 转换回list

            # 4d. 登记为beam 4
            for group_paths in final_groups.values():
                if len(group_paths) > 1:  # 确保束中至少有2条路径
                    beams[f"beam_4_common_dev_len{length}_group{beam4_idx}"] = group_paths
                    paths_to_remove_for_beam4.update(tuple(p) for p in group_paths)
                    beam4_idx += 1

        remaining_paths -= paths_to_remove_for_beam4

        # -----------------------------------------------------
        # 登记所有剩余的、未成束的路径
        # -----------------------------------------------------
        # if remaining_paths:
        #     beams["beam_other_unclassified"] = [list(p) for p in remaining_paths]

        # --- (修改) 提取内部网络 ---
        # 步骤 5: 提取所有束的内部网络
        for beam_id, paths_list in beams.items():
            for path in paths_list:
                nets_in_path = path[1::2]  # 获取所有奇数索引的元素 (网络)
                self.circuit.beam_net_sets[beam_id].update(nets_in_path)

        # 步骤 6: 生成电流束路径 (List[Set[str]]) 并存储
        # -----------------------------------------------------
        beam_paths_result: Dict[str, List[Set[str]]] = {}
        for beam_id, paths_list in beams.items():
            # if beam_id == "beam_other_unclassified":
            #     continue
            if not paths_list:
                continue  # 跳过空的电流束

            # 1. 查找该束中的最大路径长度 (这段代码完全没必要，同一束长度一定相等)
            max_len = 0
            for p in paths_list:
                path_devs = p[::2]  # <--- (修改) 适配 [Dev, Net, Dev]
                if len(path_devs) > max_len:
                    max_len = len(path_devs)

            # 2. 按索引生成集合列表，并标记器件
            current_beam_path: List[Set[str]] = []
            for i in range(max_len):
                index_set: Set[str] = set()
                for path in paths_list:
                    path_devs = path[::2]  # <--- (修改) 适配 [Dev, Net, Dev]
                    # 确保路径足够长，可以访问此索引
                    if i < len(path_devs):
                        dev_name = path_devs[i]
                        index_set.add(dev_name)
                        # --- 嵌入标签 ---
                        device = self.circuit.devices_dict.get(dev_name)
                        if device:
                            device.tags.add(self.DeviceTags.IN_CURRENT_BEAM)  #
                current_beam_path.append(index_set)

            beam_paths_result[beam_id] = current_beam_path

        # 3. 将最终结果存储在类属性中
        self.circuit.current_beam_paths = beam_paths_result
        self.circuit.current_beams = beams

    ##############################################偏置管标记################################################################
    def _mark_bias_mirrors(self):
        """
        遍历 current_cache 和 lv_current，
        根据器件是否在电流束中来标记 ..._BIAS_MIRROR 标签
        """
        for ref_name, mirror_names_list in self.current_cache.items():
            try:
                ref_device = self.circuit.devices_dict[ref_name]
                # Case 2: Ref 在电流束中，跳过 (不标记其
                if self.DeviceTags.IN_CURRENT_BEAM in ref_device.tags:  #
                    continue
                # Case 1 & 3: Ref 不在电流束中
                bias_mirror : List[str] = []
                for name in mirror_names_list:
                    dev = self.circuit.devices_dict.get(name)
                    # 如果镜像管 *不* 在电流束中，则标记为 BIAS
                    if dev and self.DeviceTags.IN_CURRENT_BEAM not in dev.tags:  #
                        dev.tags.add(self.DeviceTags.CURRENT_MIRROR_BIAS_MIRROR)  #
                        bias_mirror.append(dev.name)
                if self.DeviceTags.ROOT_REF in ref_device.tags:
                    self.root_bias_mirror[ref_device.name] = bias_mirror

            except KeyError:
                continue  # 器件在字典中但不在 devices_dict 中

        for lower_ref_name, value_list in self.lv_current.items():
            try:
                lower_ref_device = self.circuit.devices_dict[lower_ref_name]

                if self.DeviceTags.IN_CURRENT_BEAM in lower_ref_device.tags:  #
                    continue

                if self._net_matches(value_list[0],{"MOS_BIAS"}):
                    mirror_names_list = value_list[3:]  # 索引0是指示，1是上层管，2是偏置二极管
                else:
                    mirror_names_list = value_list[2:]  #没有偏置二极管

                for name in mirror_names_list:
                    dev = self.circuit.devices_dict.get(name)
                    # 如果镜像管 *不* 在电流束中，则标记为 BIAS
                    if dev and self.DeviceTags.IN_CURRENT_BEAM not in dev.tags:  #
                        dev.tags.add(self.DeviceTags.LV_MIRROR_BIAS_MIRROR)  #

            except KeyError:
                continue  # 器件在字典中但不在 devices_dict 中

    # -------------------------------------------------子结构实例检测与登记----------------------------------------------------------
    # 函数识别顺序需要优化以提高代码效率
    def _register_beam_substructures(self):
        """
        按顺序遍历电流束路径中的 *所有器件对*（避免错误），登记：
        1. 特殊或G-连接的对称对 (Diff, Out, Loads, Common) 并更新类属性
        2. 非G-连接的跨束对称对 (SYM_PAIR)，基于 *内部网络* 检查
        3.优先登记 4-器件 结构 (CMFB, Quad Load)(后续可优化识别顺序)
        """
        def _register_helper(members: List['CircuitAnalyzer.Device'], sub_type: str,
                             sub_id_prefix: str):  #
            """
                辅助函数：仅执行登记
            """
            if not members:
                return
            # 创建 sub_id
            member_names = sorted([d.name for d in members])
            sub_id = f"{sub_id_prefix}_{'_'.join(member_names)}"

            # 登记
            self.aggregate_substructure(
                sub_type=sub_type,
                members=members,
                sub_id=sub_id
            )

        # --- 辅助函数 ---
        def _check_cross_beam_symmetry(mos_a: 'CircuitAnalyzer.Device',
                                       mos_b: 'CircuitAnalyzer.Device') -> bool:  #
            """
                (新逻辑) 检查两个MOS管的栅极网络是否在同一个电流束的 *内部网络* 集合中。
            """
            g_net_a = mos_a.terminals.get("G")
            g_net_b = mos_b.terminals.get("G")

            if not g_net_a or not g_net_b:
                return False

            g_net_a_lower = g_net_a.lower()
            g_net_b_lower = g_net_b.lower()

            # 遍历在 analyze_current_beams 中生成的网络集合
            for beam_net_set in self.circuit.beam_net_sets.values():
                if self._net_matches(g_net_a, beam_net_set) and self._net_matches(g_net_b, beam_net_set):
                    return True  # 匹配成功

            return False

        # --- 构建镜像管 -> 参考管 的反向查找字典 ---
        mirror_to_ref_map: Dict[str, str] = {}
        # 1. 普通电流镜
        for ref_name, mirror_list in self.current_cache.items():
            for mirror_name in mirror_list:
                mirror_to_ref_map[mirror_name] = ref_name
        # 2. 低压电流镜 (所有镜像管都映射到 *同一个* 下层参考管键)
        for lower_ref_name, lv_list in self.lv_current.items():
            if self._net_matches(lv_list[0],{"MOS_BIAS"}):
                for mirror_name in lv_list[3:]:  # 索引0是指示，1是上层参考管，2是上层偏置管
                    mirror_to_ref_map[mirror_name] = lower_ref_name
            else:
                for mirror_name in lv_list[2:]:  # 索引0是指示，1是上层参考管
                    mirror_to_ref_map[mirror_name] = lower_ref_name
        # --- 主循环：遍历所有唯一的“对” ---
        processed_devices: Set[str] = set()
        processed_4_devices: Set[str] = set()  # 用于4器件结构

        for beam_path in self.circuit.current_beam_paths.values():
            # beam_path 是 [Set[Dev], Set[Dev], ...]
            # 我们需要获取 *器件* 集合
            beam_devices_sets = beam_path

            for element_set_names in beam_devices_sets:
                # ---优先处理 4-器件结构，避免逻辑错误 ---
                if len(element_set_names) == 4:
                    if any(element in processed_4_devices for element in element_set_names):
                        continue  # 已处理过

                    try:
                        members = [self.circuit.devices_dict[name] for name in element_set_names]
                    except KeyError:
                        continue  # 器件不存在

                    # 规则 1: 共模检测B
                    if all(self.DeviceTags.COMMON_DETECT_B in d.tags for d in members):  #
                        _register_helper(members, "共模检测B", "cmfb")
                        processed_4_devices.union(element_set_names)
                        continue  # 登记成功

                    # 规则 2: 典型负载 (基于栅极连接)
                    g_net_groups: DefaultDict[str, List['CircuitAnalyzer.Device']] = defaultdict(list)  #
                    for d in members:
                        g_net = d.terminals.get("G")
                        if g_net:
                            g_net_groups[g_net].append(d)

                    unique_g_nets = len(g_net_groups)

                    if unique_g_nets == 1:
                        # 所有 4 个栅极相连
                        for d in members: d.tags.add(self.DeviceTags.TYPICAL_LOAD)  #
                        self.typ_load.append(list(element_set_names))
                        _register_helper(members, "典型负载", "typ_load_quad")
                        processed_4_devices.union(element_set_names)
                        continue  # 登记成功

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

                        # --- 特殊或G连接的对称对 ---
                        # 规则 1: 差分输入对
                        a_is_pos = dev_a_name in self.diff_pair_positive
                        a_is_neg = dev_a_name in self.diff_pair_negative
                        b_is_pos = dev_b_name in self.diff_pair_positive
                        b_is_neg = dev_b_name in self.diff_pair_negative
                        if (a_is_pos and b_is_neg) or (a_is_neg and b_is_pos):
                            self.diff_pair.extend([dev_a.name, dev_b_name])
                            _register_helper(members, "差分输入对", "diff_pair")
                            processed_devices.add(dev_a_name)
                            processed_devices.add(dev_b_name)
                            continue  # 登记成功

                        # 规则 2: 输出对
                        if (dev_a_name in self.positive_output and dev_b_name in self.negative_output) or \
                                (dev_a_name in self.negative_output and dev_b_name in self.positive_output):
                            self.output_pair.append([dev_a.name, dev_b.name])
                            _register_helper(members, "输出对", "out_pair")
                            processed_devices.add(dev_a_name)
                            processed_devices.add(dev_b_name)
                            continue  # 登记成功

                        # 规则 3: A型负载 (二极管 + 镜像管)
                        a_is_diode = self.DeviceTags.DIODE_MOS in dev_a.tags  #
                        b_is_diode = self.DeviceTags.DIODE_MOS in dev_b.tags  #
                        a_load_match = False
                        if a_is_diode and dev_b_name in self.current_cache.get(dev_a_name, []):
                            dev_a.tags.add(self.DeviceTags.SPEC_A_LOAD_DIO)  #
                            dev_b.tags.add(self.DeviceTags.SPEC_A_LOAD_TYP)  #
                            a_load_match = True
                        elif b_is_diode and dev_a_name in self.current_cache.get(dev_b_name, []):
                            dev_b.tags.add(self.DeviceTags.SPEC_A_LOAD_DIO)  #
                            dev_a.tags.add(self.DeviceTags.SPEC_A_LOAD_TYP)  #
                            a_load_match = True
                        if a_load_match:
                            self.A_load.append([dev_a_name, dev_b_name])
                            _register_helper(members, "A型负载", "a_load")
                            processed_devices.add(dev_a_name)
                            processed_devices.add(dev_b_name)
                            continue  # 登记成功

                        # 规则 4: B型负载 (两个二极管)
                        if a_is_diode and b_is_diode:
                            dev_a.tags.add(self.DeviceTags.SPEC_B_LOAD)  #
                            dev_b.tags.add(self.DeviceTags.SPEC_B_LOAD)  #
                            self.B_load.append([dev_a_name, dev_b_name])
                            _register_helper(members, "B型负载", "b_load")
                            processed_devices.add(dev_a_name)
                            processed_devices.add(dev_b_name)
                            continue  # 登记成功

                        # 规则 5: 典型负载 (来自电流镜)
                        ref_a = mirror_to_ref_map.get(dev_a_name)
                        ref_b = mirror_to_ref_map.get(dev_b_name)
                        if ref_a is not None and ref_a == ref_b:
                            dev_a.tags.add(self.DeviceTags.TYPICAL_LOAD)  #
                            dev_b.tags.add(self.DeviceTags.TYPICAL_LOAD)  #
                            self.typ_load.append([dev_a_name, dev_b_name])
                            _register_helper(members, "典型负载", "typ_load")
                            processed_devices.add(dev_a_name)
                            processed_devices.add(dev_b_name)
                            continue  # 登记成功

                        # 规则 6: 对称对 (共模)
                        a_is_common = dev_a_name in self.common_get
                        b_is_common = dev_b_name in self.common_get
                        if a_is_common != b_is_common:  # XOR (一个是，一个不是)
                            new_dev_name = dev_b.name if a_is_common else dev_a.name
                            if new_dev_name not in self.common_get:
                                self.common_get.append(new_dev_name)
                            dev_a.tags.add(self.DeviceTags.COMMON_GET)  #
                            dev_b.tags.add(self.DeviceTags.COMMON_GET)  #
                            _register_helper(members, "对称对", "sym_pair")
                            processed_devices.add(dev_a_name)
                            processed_devices.add(dev_b_name)
                            continue  # 登记成功

                        # --- 非 G-连接的对称对 ---
                        g_net_a = dev_a.terminals.get("G")
                        g_net_b = dev_b.terminals.get("G")
                        if g_net_a and g_net_b and g_net_a != g_net_b:
                            if _check_cross_beam_symmetry(dev_a, dev_b):
                                dev_a.tags.add(self.DeviceTags.SYM_PAIR)  #
                                dev_b.tags.add(self.DeviceTags.SYM_PAIR)  #
                                self.sym_pair.append([dev_a_name, dev_b_name])
                                _register_helper(members, "对称对", "sym_pair_cross")
                                processed_devices.add(dev_a_name)
                                processed_devices.add(dev_b_name)
                                continue  # 登记成功

    # ---------------------------------------------登记低压电流镜中的对称镜像对---------------------------------------------------
    def _register_lv_mirror_pairs(self):
        """
        遍历所有电流束中的 *实际路径*，查找是否存在
        非偏置的上层镜像管和下层镜像管在路径中连续出现的情况。
        如果存在，则将它们登记为 "对称对"。
        """
        processed_pairs = set()  # 避免同一对被重复登记

        # 遍历所有电流束
        for beam_id, paths_list in self.circuit.current_beams.items():
            # 遍历该束中的每条路径
            for path in paths_list:
                devices_in_path = path[::2]  # 只获取器件名称 (偶数索引)

                if len(devices_in_path) < 2:
                    continue

                # 遍历路径中所有 *连续的* 器件对
                for i in range(len(devices_in_path) - 1):
                    dev_a_name = devices_in_path[i]
                    dev_b_name = devices_in_path[i + 1]

                    # 检查是否已处理 (排序以确保 frozenset 唯一)
                    pair_fset = frozenset([dev_a_name, dev_b_name])
                    if pair_fset in processed_pairs:
                        continue

                    try:
                        dev_a = self.circuit.devices_dict[dev_a_name]
                        dev_b = self.circuit.devices_dict[dev_b_name]
                    except KeyError:
                        continue  # 器件不存在

                    # --- 检查核心逻辑 ---
                    # 1. 检查是否为非偏置管
                    is_bias_a = self.DeviceTags.LV_MIRROR_BIAS_MIRROR in dev_a.tags
                    is_bias_b = self.DeviceTags.LV_MIRROR_BIAS_MIRROR in dev_b.tags
                    if is_bias_a or is_bias_b:
                        continue  # 任意一个是偏置管，则跳过

                    # 2. 检查是否为 上/下 镜像对
                    is_upper_a = self.DeviceTags.LV_MIRROR_UPPER_MIRROR in dev_a.tags
                    is_lower_a = self.DeviceTags.LV_MIRROR_LOWER_MIRROR in dev_a.tags
                    is_upper_b = self.DeviceTags.LV_MIRROR_UPPER_MIRROR in dev_b.tags
                    is_lower_b = self.DeviceTags.LV_MIRROR_LOWER_MIRROR in dev_b.tags

                    is_pair_match = (is_upper_a and is_lower_b) or (is_lower_a and is_upper_b)

                    if is_pair_match:
                        # 3. 登记
                        dev_a.tags.add(self.DeviceTags.LV_MIRROR_PAIR)
                        dev_b.tags.add(self.DeviceTags.LV_MIRROR_PAIR)

                        self.aggregate_substructure(
                            sub_type="对称对",
                            members=[dev_a, dev_b],
                            sub_id=f"lv_mirror_pair_{dev_a_name}_{dev_b_name}"
                        )

                        processed_pairs.add(pair_fset)

    # ---------------------------------------------登记低压电流镜 ---------------------------------------------------
    def _register_lv_mirrors(self):
        """
        遍历 self.lv_current 缓存，登记低压电流镜子结构。
        """
        for lower_ref_name, value_list in self.lv_current.items():
            # value_list = [sign, upper_ref_name, (upper_bias_name), mirror1, mirror2, ...]
            # 完整的成员列表 = [lower_ref] + [upper_ref] + ([upper_bias]) + [mirrors]
            all_member_names = [lower_ref_name] + value_list[1:]

            # 获取 Device 对象
            all_members: List['CircuitAnalyzer.Device'] = []  #
            for name in all_member_names:
                device = self.circuit.devices_dict.get(name)
                if device:
                    all_members.append(device)
                else:
                    print(f"警告：在登记低压电流镜 {lower_ref_name} 时未找到器件 {name}。")

            if not all_members:
                continue

            self.aggregate_substructure(
                sub_type="低压电流镜",
                members=all_members,
                sub_id=f"lv_mirror_{lower_ref_name}"
            )

    # -----------------------------------------------登记普通电流镜 --------------------------------------------------
    def _register_current_mirrors(self):
        """
        遍历 self.current_cache 缓存，登记普通电流镜子结构。
        (此时缓存已被LV镜逻辑清洗过)
        """
        for ref_name, mirror_names_list in self.current_cache.items():

            # 获取 Device 对象
            ref_device = self.circuit.devices_dict.get(ref_name)
            if not ref_device:
                print(f"警告：在登记普通电流镜时未找到参考管 {ref_name}。")
                continue

            all_members: List['CircuitAnalyzer.Device'] = [ref_device]  #
            for name in mirror_names_list:
                device = self.circuit.devices_dict.get(name)
                if device:
                    all_members.append(device)
                else:
                    print(f"警告：在登记普通电流镜 {ref_name} 时未找到镜像管 {name}。")

            # 确保至少有1个参考管和1个镜像管
            if len(all_members) < 2:
                continue

            self.aggregate_substructure(
                sub_type="普通电流镜",
                members=all_members,
                sub_id=f"current_mirror_{ref_name}"
            )

    # ---------------------------------------缓存尾电流源--------------------------------------------
    def _get_tail_current(self):
        """
        识别电路中的尾电流源：
        1. 输入回路 (beam_1_differential): 长度为1的元素 -> input_tail
        2. 公共部分 (Overlap): 检测 beam_1 和 beam_2 的重合元素，提取共栅对 -> common_tail
        3. 输出回路 (beam_2_output): 剔除重合元素后，根据典型负载和低压镜像对标签提取 -> output_tail
        """
        # 获取路径数据，若不存在则返回
        path1 = self.circuit.current_beam_paths.get("beam_1_differential")
        path2 = self.circuit.current_beam_paths.get("beam_2_output")

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
                self.input_tail.append(dev_name)

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

                    g_a = dev_a.terminals.get("G")
                    g_b = dev_b.terminals.get("G")

                    # 检查栅极是否连接在一起
                    if self._net_matches(g_a, {g_b}):
                        self.common_tail.append([name_a, name_b])
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
            has_typ_load = self.DeviceTags.TYPICAL_LOAD in dev.tags
            has_lv_mirror_pair = self.DeviceTags.LV_MIRROR_PAIR in dev.tags

            # 规则: 若不存在典型负载标签，直接跳过
            if not has_typ_load:
                i += 1
                continue

            # 存在典型负载标签
            if not has_lv_mirror_pair:
                # 情况 A: 不存在低压电流镜对称对标签
                # 存入当前两个管子 [A, B]
                self.output_tail.append(current_list)
                i += 1
            else:
                # 情况 B: 存在低压电流镜对称对标签
                # 存入当前两个 + 下一个元素的两个 [A, B, C, D]
                # 基于逻辑保证：下一个元素一定存在
                if i + 1 < n:
                    next_list = list(filtered_path2[i + 1])
                    combined_list = current_list + next_list
                    self.output_tail.append(combined_list)
                    # 跳过下一个元素，处理下下个
                    i += 2
                else:
                    # 异常情况防越界（理论不应到达）
                    i += 1

    #--------------------------------------------------真正输出对----------------------------------------------------
    def _get_vip_pair(self):
        """
        识别关键输出对 (VIP Output Pair)。
        定义：对于一个输出对，如果这两个管子的栅极网络在第一个电流束 (beam_1_differential)
        的电流束网络集合中，则它们构成关键输出对。
        """
        # 1. 获取第一个电流束的网络集合
        # 对应 "beam_net_sets中第一个键的值"
        beam1_nets = self.circuit.beam_net_sets.get("beam_1_differential")

        if not beam1_nets:
            return

        # 为了确保匹配的健壮性，使用小写集合进行比较 (与 _net_matches 逻辑保持一致)
        beam1_nets_lower = {n.lower() for n in beam1_nets}

        # 2. 遍历 output_pair 中的元素
        for pair in self.output_pair:
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
                # 存入 self.vip_output_pair
                self.vip_output_pair = pair
                # 结束循环 (VIP输出对要么没有，要么只有一对)
                break

    # ------------------------------------------登记频率补偿和共模检测A ------------------------------------------------
    def _register_rc_structures(self):
        """
        遍历 RC 缓存，登记 频率补偿 和 共模检测A 子结构。
        """
        # 1. 登记 频率补偿
        if self.compensate:
            members: List['CircuitAnalyzer.Device'] = []  #
            # 使用 set 确保器件唯一
            for name in set(self.compensate):
                dev = self.circuit.devices_dict.get(name)
                if dev:
                    members.append(dev)

            if members:
                self.aggregate_substructure(
                    sub_type="频率补偿",
                    members=members,
                    sub_id="compensate_rc_global"
                )

        # 2. 登记 共模检测A
        if self.common_detect_a:
            members: List['CircuitAnalyzer.Device'] = []  #
            # 使用 set 确保器件唯一
            for name in set(self.common_detect_a):
                dev = self.circuit.devices_dict.get(name)
                if dev:
                    members.append(dev)

            if members:
                self.aggregate_substructure(
                    sub_type="共模检测A",
                    members=members,
                    sub_id="common_detect_a_rc_global"
                )

    # -------------------------------------------登记对称电容-------------------------------------------
    def _register_sym_capacitors(self):
        """
            遍历所有未被分配的电容, 检查对称性。
        """
        # 1. 收集候选电容
        excluded_caps = set(self.compensate).union(set(self.common_detect_a))
        caps_to_check = [
            d for d in self.circuit.devices_dict.values()
            if d.type == "Capacitor" and d.name not in excluded_caps
        ]

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

                c1_pwr = (self._is_net_power(c1_net1), self._is_net_power(c1_net2))
                c2_pwr = (self._is_net_power(c2_net1), self._is_net_power(c2_net2))

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
                    c1.tags.add(self.DeviceTags.SYM_CAPACITOR)  #
                    c2.tags.add(self.DeviceTags.SYM_CAPACITOR)  #
                    self.capacitor_pair.append([c1.name, c2.name])

                    # 登记
                    self.aggregate_substructure(
                        sub_type="对称电容",
                        members=[c1, c2],
                        sub_id=f"sym_cap_{c1.name}_{c2.name}"
                    )
                    # 标记为已处理
                    processed_caps.add(c1.name)
                    processed_caps.add(c2.name)
                    # 找到了 c1 的配对，跳出内层循环，开始找下一个 c1
                    break

    # -------------------------------------子结构实例登记函数-----------------------------------------
    def aggregate_substructure(self, sub_type: str, members: List['CircuitAnalyzer.Device'],
                               sub_id: str):  #
        """
        将一组器件登记为一个子结构实例。
        """
        sub_def = self.circuit.substructure_types.get(sub_type)
        if not sub_def:
            return
        member_roles = set().union(*[d.tags for d in members])
        if not sub_def.aggregation_rule(member_roles):
            return
        try:
            constraints = sub_def.constraint_rules(members)
        except Exception as e:
            traceback.print_exc()
            return

        self.circuit.substructures.append(self.CircuitSub(  #
            sub_id=sub_id,
            type=sub_type,
            members=[d.name for d in members],
            constraints=constraints
        ))

        for device in members:
            device.substructures.append(self.DeviceSub(sub_type=sub_type, sub_id=sub_id))  #


    #----------------------------------------------------约束生成------------------------------------------------------------
    def _generate_constraint_groups(self):
        """
        遍历所有已登记子结构的约束，构建参数依赖图。
        使用DFS查找图中的所有连通分量 (受约束的参数)。
        添加所有未受约束的独立参数。
        将最终结果存储在 self.constraint_groups 中。
        """
        adj_list: DefaultDict[str, Set[str]] = defaultdict(set)

        # 1. 构建邻接表
        for instance in self.circuit.substructures:
            for constraint_str in instance.constraints:
                try:
                    # 解析 "param_a = param_b" 格式
                    parts = constraint_str.split("=")
                    if len(parts) != 2:
                        continue  # 忽略格式错误的约束

                    param_a = parts[0].strip()
                    param_b = parts[1].strip()

                    # 添加无向边 (格式已在约束函数中改为 '_')
                    if param_a and param_b:
                        adj_list[param_a].add(param_b)
                        adj_list[param_b].add(param_a)
                except Exception:
                    # 捕获潜在的解析错误
                    print(f"警告：无法解析约束 '{constraint_str}'")
                    continue

        # 2. 获取 *所有* 可能的参数
        all_params_set: Set[str] = set()
        for device in self.circuit.devices_dict.values():
            for param_key in device.params.keys():
                all_params_set.add(f"{device.name}_{param_key}")  #

        # 3. 查找连通分量 (受约束的参数)
        visited: Set[str] = set()
        all_components: List[List[str]] = []

        for param in adj_list:  # 只需要从有约束的参数开始遍历
            if param not in visited:
                # 发现新组件，开始DFS
                current_component: List[str] = []
                stack: List[str] = [param]

                while stack:
                    node = stack.pop()
                    if node not in visited:
                        visited.add(node)
                        current_component.append(node)

                        # 将所有未访问的邻居加入栈
                        for neighbor in adj_list[node]:
                            if neighbor not in visited:
                                stack.append(neighbor)

                # 排序以保证输出一致性 (可选，但推荐)
                current_component.sort()
                all_components.append(current_component)

        # 4. 添加所有独立的 (未受约束的) 参数
        for param in all_params_set:
            if param not in visited:
                all_components.append([param])  # 添加为长度为1的列表

        # 5. 存储结果到 Analyzer 属性
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

    def _is_copy_tube(self, target_param_name: str, ref_param_name: str) -> bool:
        """
        辅助函数：检查一个 'l' 参数是否属于"复制管"。
        """
        try:
            target_dev_name, key = target_param_name.rsplit("_", 1)
            if key != 'l':  # 补偿只适用于 'l'
                return False

            ref_dev_name, _ = ref_param_name.rsplit("_", 1)

            target_dev = self.circuit.devices_dict[target_dev_name]
            ref_dev = self.circuit.devices_dict[ref_dev_name]
        except (KeyError, ValueError, AttributeError):
            return False

        # --- 检查普通电流镜 (V6 定义 1.1, 1.2) ---
        if ref_dev_name in self.current_cache and target_dev_name in self.current_cache[ref_dev_name]:
            is_ref_in_beam = self.DeviceTags.IN_CURRENT_BEAM in ref_dev.tags
            is_ref_root = self.DeviceTags.ROOT_REF in ref_dev.tags
            if is_ref_in_beam or is_ref_root:
                return True
            else:
                return self.DeviceTags.IN_CURRENT_BEAM in target_dev.tags

        # --- 检查低压电流镜 (V6 定义 2.1 - 2.4) ---
        lv_sub_ref = next((s for s in target_dev.substructures if s.sub_type == "低压电流镜"), None)
        if not lv_sub_ref:
            return False  # B 不是 LV 镜像管

        lv_sub = next((s for s in self.circuit.substructures if s.sub_id == lv_sub_ref.sub_id), None)
        if not lv_sub:
            return False  # 找不到子结构实例

        try:
            members = {name: self.circuit.devices_dict[name] for name in lv_sub.members}
            upper_bias_dev = next((d for d in members.values() if self.DeviceTags.LV_MIRROR_UPPER_BIAS in d.tags))

            # 找到 "上层管" (非二极管连接的那个)
            upper_ref_dev = next((d for d in members.values() if
                                    self.DeviceTags.LV_MIRROR_UPPER_REF in d.tags
                                    and self.DeviceTags.DIODE_MOS not in d.tags))
        except (StopIteration, KeyError):
            print(f"警告：在 {lv_sub.sub_id} 中找不到 LV 关键器件，无法应用补偿。")
            return False

        is_coupled = upper_bias_dev
        is_in_beam = self.DeviceTags.IN_CURRENT_BEAM in upper_ref_dev.tags
        is_bias_mirror = self.DeviceTags.LV_MIRROR_BIAS_MIRROR in target_dev.tags

        # (2.1) 独立 & 在束
        if not is_coupled and is_in_beam:
            return True  # B 是所有镜像管

        # (2.2) 独立 & 偏置
        if not is_coupled and not is_in_beam:
            return not is_bias_mirror  # B 是所有非偏置镜像管

        # (2.3) 耦合 & 在束
        if is_coupled and is_in_beam:
            return True  # B 是所有镜像管

        # (2.4) 耦合 & 偏置
        if is_coupled and not is_in_beam:
            return not is_bias_mirror  # B 是所有非偏置镜像管

        return False

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
        """
        print("\n" + "=" * 30 + " 预计算 r_raw 真值 " + "=" * 30)
        # 使用 self.device_params (原始CDF值)
        params_dict = self.device_params

        # 1. 处理普通电流镜
        for ref_name, mirror_list in self.current_cache.items():
            ref_wl = self._get_w_over_l(ref_name, params_dict)
            if ref_wl is None:
                print(f"  [警告] CM Ref {ref_name} W/L 计算失败，跳过其镜像管。")
                continue

            for copy_name in mirror_list:
                # 使用 _is_copy_tube 检查（尽管这里大部分都是）
                if self._is_copy_tube(f"{copy_name}_l", f"{ref_name}_l"):
                    copy_wl = self._get_w_over_l(copy_name, params_dict)
                    if copy_wl is None:
                        print(f"  [警告] CM Copy {copy_name} W/L 计算失败。")
                        continue

                    if ref_wl == 0.0:
                        print(f"  [警告] CM Ref {ref_name} W/L 为 0，无法计算 r_raw。")
                        continue

                    r_raw = copy_wl / ref_wl
                    self.copy_tube_r_raw_map[copy_name] = (ref_name, r_raw)
                    print(f"  [CM] 记录 {copy_name} (Ref: {ref_name}), r_raw = {r_raw:.4f}")

        # 2. 处理低压电流镜
        # lv_current 格式: {lower_ref_name: [sign, upper_ref, (upper_bias), mirror1, mirror2, ...]}
        for lower_ref_name, value_list in self.lv_current.items():
            # --- 必须为上/下层管分别计算 W/L 参考 ---

            # 2a. 获取下层参考管 W/L
            lower_ref_wl = self._get_w_over_l(lower_ref_name, params_dict)
            if lower_ref_wl is None:
                print(f"  [警告] LV Ref {lower_ref_name} W/L 计算失败，跳过其镜像管。")
                continue

            # 2b. 查找 'upper_ref' 管 (与 _is_copy_tube 逻辑一致)
            upper_ref_name = value_list[1]
            try:
                # 找到子结构实例
                lower_ref_dev = self.circuit.devices_dict[lower_ref_name]
                lv_sub_ref = next((s for s in lower_ref_dev.substructures if s.sub_type == "低压电流镜"), None)
                if not lv_sub_ref:
                    print(f"  [警告] LV Ref {lower_ref_name} 找不到子结构引用。")
                    continue

                lv_sub = next((s for s in self.circuit.substructures if s.sub_id == lv_sub_ref.sub_id), None)
                if not lv_sub:
                    print(f"  [警告] LV Ref {lower_ref_name} 找不到子结构实例 {lv_sub_ref.sub_id}。")
                    continue

            except StopIteration:
                print(f"  [警告] LV 组 {lower_ref_name} 发生未知错误，无法计算上层 r_raw。")
                continue
            except Exception as e:
                print(f"  [警告] LV 组 {lower_ref_name} 发生未知错误: {e}")
                continue

            upper_ref_wl = self._get_w_over_l(upper_ref_name, params_dict)

            if upper_ref_wl is None:
                print(f"  [警告] LV Upper Ref {upper_ref_name} W/L 计算失败。")
                continue
            #筛出镜像管
            if self._net_matches(value_list[0],{"MOS_BIAS"}):
                member_lists = value_list[3:]
            else:
                member_lists = value_list[2:]

            # 2c. 遍历所有可能的复制管，并应用修正后的 r_raw 逻辑
            for copy_name in member_lists:
                # 检查 copy_name 是否是复制管 (参考 lower_ref_name, 这仍然是分组的 KEY)
                if not self._is_copy_tube(f"{copy_name}_l", f"{lower_ref_name}_l"):
                    continue

                copy_dev = self.circuit.devices_dict.get(copy_name)
                if not copy_dev: continue

                copy_wl = self._get_w_over_l(copy_name, params_dict)
                if copy_wl is None:
                    print(f"  [警告] LV Copy {copy_name} W/L 计算失败。")
                    continue

                # --- 根据标签选择正确的参考 ---
                target_ref_wl = None
                target_ref_name = None

                # 规则 1: "如果“复制管”有上层镜像管的标签..."
                if self.DeviceTags.LV_MIRROR_UPPER_MIRROR in copy_dev.tags:
                    target_ref_wl = upper_ref_wl
                    target_ref_name = upper_ref_name
                # 规则 2: "如果“复制管”有下层镜像管的标签..."
                elif self.DeviceTags.LV_MIRROR_LOWER_MIRROR in copy_dev.tags:
                    target_ref_wl = lower_ref_wl
                    target_ref_name = lower_ref_name
                else:
                    # 回退 (例如，如果标记不完整，虽然不应发生)
                    print(
                        f"  [信息] LV Copy {copy_name} (Tags: {copy_dev.tags}) 未匹配上/下层特定逻辑，回退到下层参考 {lower_ref_name}。")
                    target_ref_wl = lower_ref_wl
                    target_ref_name = lower_ref_name

                if target_ref_wl is None or target_ref_wl == 0.0:
                    print(f"  [警告] LV Copy {copy_name} 的目标参考 {target_ref_name} W/L 为 0 或 None。")
                    continue

                r_raw = copy_wl / target_ref_wl

                # 存储：键仍然是 lower_ref_name (用于分组)，值是 (lower_ref_name, r_raw)
                self.copy_tube_r_raw_map[copy_name] = (lower_ref_name, r_raw)
                # 打印时显示 *实际* 使用的参考
                print(f"  [LV] 记录 {copy_name} (实际参考: {target_ref_name}), r_raw = {r_raw:.4f}")

        print("=" * 30 + " r_raw 预计算完成 " + "=" * 30)

    # ----------------------------------------------------- 两阶段校准 -----------------------------------------------------------
    def _calibrate_device_params(self):
        """
        基于两阶段校准：
        1. 阶段一：应用非电流镜约束（允许“污染”复制管），推迟电流镜约束。
        2. 阶段二：在最后，基于 r_raw 真值对复制管进行最终补偿。
        """
        # 0. 目标字典和约束组
        new_device_params = copy.deepcopy(self.device_params)
        groups_to_process = self.constraint_groups

        TAG_PRIORITY_ORDER = [
            self.DeviceTags.ROOT_REF,
            self.DeviceTags.CURRENT_MIRROR_REF,
            self.DeviceTags.LV_MIRROR_LOWER_REF,
            self.DeviceTags.CASCODE_MAIN
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
                    if (self.DeviceTags.CURRENT_MIRROR_REF in dev_tags or
                            self.DeviceTags.LV_MIRROR_LOWER_REF in dev_tags):
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
                    # 数学上, W_new/W_ref = r_raw_target (因为 L_new=L_ref)
                    if abs(r_now_W_ratio - r_raw_target) > 1e-9:
                        print(f"    [补偿需求]: r_now_W ({r_now_W_ratio:.4f}) != r_raw_target ({r_raw_target:.4f})")

                        # W_new = W_ref_now * r_raw_target
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
    lib_path = "2025_EDA_case1"
    cell_name = "OPA"
    view_name = "schematic"

    param_file = os.path.join(os.getcwd(), "case1_extractcdfVal_0.txt")

    if not os.path.exists(param_file):
        raise FileNotFoundError(f"参数文件不存在：{param_file}")
    # 计算两字典
    try:
        param_manager = ParameterManager(param_file)
    except Exception as e:
        traceback.print_exc()
        raise RuntimeError(f"参数管理器初始化失败：{str(e)}") from e
    # 进行电路分析
    try:
        #: 实例化主类
        analyzer = CircuitAnalyzer(
            lib=lib_path,
            cell=cell_name,
            view=view_name,
            param_manager=param_manager,
            power_positive={"VDD_1P8"}  # 自定义电源集合
        )
    except Exception as e:
        traceback.print_exc()
        raise RuntimeError(f"分析器初始化失败：{str(e)}") from e

    # ---  测试代码 ---
    print("\n" + "=" * 30 + " 测试输出 " + "=" * 30)

    # 1. 检查器件数量
    print(f"\n[电路基本信息]")
    print(f"  识别到的器件总数: {len(analyzer.circuit.devices_dict)}")

    # 2. 检查部分器件的标签和所属子结构
    print(f"\n[部分器件详情]")
    devices_to_check = ["NM0", "PM0", "R0", "C0"]  # 示例器件
    for name in devices_to_check:
        dev = analyzer.circuit.devices_dict.get(name)
        if dev:
            print(f"  器件 {name}:")
            print(f"    类型: {dev.type}")
            print(f"    标签: {dev.tags}")
            print(f"    所属子结构: {[f'{s.sub_type}({s.sub_id})' for s in dev.substructures]}")
        else:
            print(f"  器件 {name}: 未找到")

    # 3. 检查缓存内容
    print(f"\n[缓存内容]")
    print(f"  差分正输入管 (diff_pair_positive): {analyzer.diff_pair_positive}")
    print(f"  差分负输入管 (diff_pair_negative): {analyzer.diff_pair_negative}")
    print(f"  差分输入对 (diff_pair): {analyzer.diff_pair}\n")

    print(f"  正端输出管 (output_positive): {analyzer.positive_output}")
    print(f"  负端输出管 (output_negative): {analyzer.negative_output}")
    print(f"  输出对 (output_pair): {analyzer.output_pair}")
    print(f"    真正输出对(vip_output_pair): {analyzer.vip_output_pair}\n")

    print(f"  级联缓存 (cascode_cache): {analyzer.cascode_cache}")
    print(f"  普通电流镜缓存 (current_cache): {analyzer.current_cache}")
    print(f"  根参考管镜像管缓存 (root_bias_mirror): {analyzer.root_bias_mirror}")
    print(f"  低压电流镜缓存 (lv_current): {analyzer.lv_current}\n")

    print(f"  频率补偿缓存 (compensate): {analyzer.compensate}")
    print(f"  共模检测A缓存 (common_detect_a): {analyzer.common_detect_a}")
    print(f"  对称电容对 (capacitor_pair): {analyzer.capacitor_pair}\n")

    print(f"  共模检测B缓存 (common_detect_b): {analyzer.common_detect_b}")
    print(f"  共模输入对 (common_get): {analyzer.common_get}\n")

    print(f"  A型负载 (A_load): {analyzer.A_load}")
    print(f"  B型负载 (B_load): {analyzer.B_load}")
    print(f"  典型负载 (typ_load): {analyzer.typ_load}")
    print(f"  对称对 (sym_pair): {analyzer.sym_pair}\n")

    print(f"    输入尾电流源(input_tail): {analyzer.input_tail}")
    print(f"    输出电流源(output_tail): {analyzer.output_tail}")
    print(f"    公共尾电流源(common_tail): {analyzer.common_tail}\n")

    # 4. 检查电流路径
    print("\n[电流路径]")
    if analyzer.circuit.current_paths:
        for i, path in enumerate(analyzer.circuit.current_paths, 1):
            print(f"  路径{i}: {' -> '.join(path)}")
    else:
        print("  未生成电流路径。")

    # 5. 检查电流束
    current_beams = analyzer.circuit.current_beams
    print("\n[电流束分析结果]")
    if current_beams:
        for beam_id, paths in current_beams.items():
            print(f"  电流束: {beam_id} (包含 {len(paths)} 条路径)")
            # for i, path in enumerate(paths, 1):
            #     print(f"    - 路径 {i}: {' -> '.join(path)}") # 详细路径可选
    else:
        print("  未分析出电流束。")

    # 6. 检查电流束路径
    print("\n[电流束路径 (Beam Paths)]")
    if analyzer.circuit.current_beam_paths:
        for beam_id, beam_path in analyzer.circuit.current_beam_paths.items():
            print(f"  电流束: {beam_id}")
            path_str = " -> ".join([
                str(s) if len(s) > 1 else list(s)[0] if len(s) == 1 else "{}"
                for s in beam_path
            ])
            print(f"    - 束路径: {path_str}")
    else:
        print("  未生成电流束路径。")

    # 7.电流束内部网络
    print(f"\n[电流束内部网络 (Beam Net Sets)]")
    if analyzer.circuit.beam_net_sets:
        for beam_id, net_set in analyzer.circuit.beam_net_sets.items():
            print(f"  电流束: {beam_id} (包含 {len(net_set)} 个内部网络)")
            print(f"    - 网络: {net_set}")  # 详细网络可选
    else:
        print("  未生成电流束内部网络。")

    # 8. 检查登记的子结构实例
    print("\n[登记的子结构实例]")
    if analyzer.circuit.substructures:
        for i, sub in enumerate(analyzer.circuit.substructures, 1):
            print(f"  实例 {i}:")
            print(f"    ID: {sub.sub_id}")
            print(f"    类型: {sub.type}")
            print(f"    成员: {sub.members}")
            print(f"    约束: {sub.constraints}")  # 约束较长，可选打印
    else:
        print("  未登记任何子结构实例。")

    # 9. 电路独立参数列表
    print("\n[全局约束组 (Constraint Groups)]")
    if analyzer.constraint_groups:
        print(f"  共找到 {len(analyzer.constraint_groups)} 个等效参数组 (包含独立参数)：")
        for i, group in enumerate(analyzer.constraint_groups, 1):
            print(f"  组 {i}: {group}")
    else:
        print("  未生成任何全局约束组。")

    # 10，电路修改后的初始解
    print(analyzer.calibrate_params)

    print("\n" + "=" * 28 + " 测试输出结束 " + "=" * 28)