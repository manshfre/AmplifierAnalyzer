import os
import copy
import traceback
import json
import itertools
from typing import Dict, List, Callable, Set, Mapping, Optional, DefaultDict
from types import MappingProxyType
from collections import defaultdict
from parameter_manager import ParameterManager

# ------------------------------
# 常量定义：器件标签集中管理
# ------------------------------
class DeviceTags:
    DIODE_MOS = "二极管连接MOS管"
    # ---------------------级联----------------------
    CASCODE_MAIN = "主级联"
    CASCODE_SLAVE = "从级联"
    # -------------------对称对----------------------
    DIFF_POSITIVE = "正端输入管"
    DIFF_NEGATIVE = "负端输入管"

    SYM_PAIR = "栅极对称管"  # 栅极接到对称电流支路的管子

    OUTPUT_POSITIVE = "正端输出管"
    OUTPUT_NEGATIVE = "负端输出管"
    # --------------------电流镜----------------------
    LV_MIRROR_UPPER_REF = "上层参考管"  # 上层管子不连二极管时才有这个标签
    LV_MIRROR_UPPER = "上层管" #上层管子连二极管
    LV_MIRROR_LOWER_REF = "下层参考管"
    LV_MIRROR_UPPER_MIRROR = "上层镜像管"
    LV_MIRROR_LOWER_MIRROR = "下层镜像管"
    LV_MIRROR_BIAS_MIRROR = "偏置镜像管"
    LV_MIRROR_PAIR = "镜像对管"

    CURRENT_MIRROR_REF = "电流镜参考管"
    CURRENT_MIRROR_MIRROR = "电流镜镜像管"
    CURRENT_MIRROR_BIAS_MIRROR = "电流镜偏置镜像管"
    ROOT_REF = "根参考管"   #处在电流源路径中

    IN_CURRENT_BEAM = "处在电流束"  # 用来判断是否为偏置管
    # ----------------------负载------------------------
    SPEC_A_LOAD_DIO = "A型二极管负载"
    SPEC_A_LOAD_TYP = "A型典型负载"  #有源电流镜负载

    SPEC_B_LOAD = "B型负载"    #双二极管

    TYPICAL_LOAD = "典型负载"
    # ----------------共模检测----------------------
    COMMON_DETECT_A = "RC共模检测"

    COMMON_GET = "共模输入管"
    COMMON_OUT = "共模输出管"
    COMMON_DETECT_B = "4管共模检测"
    # ----------------------RC频率补偿-----------------------
    COMPENSATE = "频率补偿"
    # --------------------------滤波--------------------------
    SYM_CAPACITOR = "对称电容"


# ----------------用于设定器件所属子结构实例----------------
class SubStructureRef:
    def __init__(self, sub_type: str, sub_id: str):
        self.sub_type = sub_type
        self.sub_id = sub_id


# ------------------用于设定电路子结构实例------------------
class SubStructureInstance:
    def __init__(self, sub_id: str, type: str, members: List[str], constraints: List[str]):
        self.sub_id = sub_id
        self.type = type
        self.members = members
        self.constraints = constraints


class Device:
    def __init__(self, name: str, type: str, terminals: Dict[str, str], params: Dict[str, str], tags: Set[str] = None,
                 substructures: List[SubStructureRef] = None):
        self.name = name
        self.type = type
        self.terminals = terminals
        self.params = params
        self.tags = set() if tags is None else tags
        self.substructures = [] if substructures is None else substructures


# --------------------用于子结构注册-------------------
class SubStructureType:
    def __init__(self, type_name: str, required_roles: Set[str], constraint_rules: Callable[[List[Device]], List[str]],
                 aggregation_rule: Callable):
        self.type_name = type_name
        self.required_roles = required_roles
        self.constraint_rules = constraint_rules
        self.aggregation_rule = aggregation_rule


class Circuit:
    def __init__(self, devices: Dict[str, Device] = None,
                 substructure_types: Dict[str, SubStructureType] = None,
                 substructures: List[SubStructureInstance] = None,
                 current_paths: List[List[str]] = None,
                 current_beams: Dict[str, List[List[str]]] = None,
                 current_beam_paths: Dict[str, List[Set[str]]] = None,
                 beam_net_sets: Dict[str, Set[str]] = None
                 ):
        self.devices = {} if devices is None else devices
        self.substructure_types = {} if substructure_types is None else substructure_types
        self.substructures = [] if substructures is None else substructures
        self.current_paths = [] if current_paths is None else current_paths     #电流路径
        self.current_beams = {} if current_beams is None else current_beams     #电流束
        self.current_beam_paths = {} if current_beam_paths is None else current_beam_paths      #电流束路径
        self.beam_net_sets = {} if beam_net_sets is None else beam_net_sets     #电流束网络

# ------------------------------
# 核心电路分析器
# ------------------------------
class CircuitAnalyzer:
    # 1. 定义默认集合常量,集中维护,便于修改
    _DEFAULT_POWER_POSITIVE = {"VDD", "AVDD", "VDDA", "VDD_CORE", "VCC"}
    _DEFAULT_POWER_NEGATIVE = {"VSS", "AVSS", "VSSA", "GND", "VEE", "GNDA", "gnd!"}
    _DEFAULT_INPUT_NEGATIVE = {"VINN", "VIN1", "VIN_NEG", "INN", "VIN-"}
    _DEFAULT_INPUT_POSITIVE = {"VINP", "VIN2", "VIN_POS", "INP", "VIN+"}
    _DEFAULT_OUTPUT_NEGATIVE = {"VOUTN", "VOUT1", "VOUT_NEG", "OUTN", "VOUT-"}
    _DEFAULT_OUTPUT_POSITIVE = {"VOUTP", "VOUT2", "VOUT_POS", "OUTP", "VOUT+"}
    _DEFAULT_COMMON_SIGN = {"VCM", "VCOM"}
    _DEFAULT_CURRENT_SOURCE = {"IREF", "IIN"}

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
            current_source: Optional[Set[str]] = None,
            terminals_cache_file: Optional[str] = None
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
        self.circuit = Circuit()
        self.param_manager = param_manager
        self.device_types: Mapping[str, str] = MappingProxyType(
            copy.deepcopy(param_manager.device_types)
        )
        self.device_params: Mapping[str, Dict[str, str]] = MappingProxyType(
            copy.deepcopy(param_manager.device_params)
        )

        # --- 离线模式相关属性 ---
        self.terminals_cache_file = terminals_cache_file
        self._all_terminals_map: Dict[str, Dict[str, str]] = {}
        self._offline_mode = False

        self._cv = None  # Aether电路视图对象
        self.net_device_map: DefaultDict[str, List[str]] = defaultdict(list)  # 网络-器件映射,网络名小写
        # -------------------------------------缓存初始化---------------------------------------
        self.diff_pair_negative: List[str] = []  # 临时存储差分管
        self.diff_pair_positive: List[str] = []
        self.diff_pair: List[str] = []    #输入对

        self.common_get: List[str] = []  # 共模输入对
        self.common_detect_b: List[str] = []    #4管共模检测

        self.positive_output: List[str] = []  # 临时存储输出管
        self.negative_output: List[str] = []
        self.output_pair: List[List[str]] = []  #输出对

        self.compensate: List[str] = []     #频率补偿
        self.common_detect_a: List[str] = []    #RC共模检测
        self.capacitor_pair: List[List[str]] = []   #对称电容（滤波电容）

        self.cascode_cache: Dict[str, List[str]] = {}   #级联

        self.current_cache: Dict[str, List[str]] = {}  # 普通电流镜，先生成，后会被低压电流镜删减
        self.root_bias_mirror : Dict[str,List[str]] = {}
        self.lv_current: Dict[str, List[str]] = {}  #低压电流镜
        
        self.sym_pair : List[List[str]] = []    #栅极接对称电流支路的管子
        self.typ_load : List[List[str]] = []    #典型负载
        self.A_load : List[List[str]] = []      #有源电流镜负载
        self.B_load : List[List[str]] = []      #二极管负载
        
        self.top_nodes: List[Device] = []  # 顶层节点器件列表
        self._flat_beam_cache: Optional[List[Set[str]]] = None  # 用于缓存压平的电流束路径
        self.circuit.beam_net_sets = defaultdict(set)

        self.constraint_groups: List[List[str]]= []     #输出参数列表


        try:
            # 检查是否进入离线模式
            if self.terminals_cache_file and os.path.exists(self.terminals_cache_file):
                self._offline_mode = True
                print(f"--- 运行于 OFFLINE 模式。正在从 {self.terminals_cache_file} 加载... ---")
                self._load_terminals_from_cache()
            else:
                self._offline_mode = False
                if self.terminals_cache_file:
                    print(f"--- 缓存文件 {self.terminals_cache_file} 未找到。 ---")
                print("--- 运行于 ONLINE 模式。正在初始化 pyAether... ---")
                # --------------------------------BOOT,打开对应原理图-------------------------------

            # ------------------- 读取/生成器件连接导线/参数/建立网络-器件映射/创建Device实例--------------
            self._init_device_terminals()

        except Exception as e:
            traceback.print_exc()
            raise RuntimeError(f"电路初始化失败：{str(e)}") from e

        # -----------------------------------------子结构注册-----------------------------------------------
        self._register_substructure_types()

        # ----------------------------------------特殊器件检测---------------------------------------------
        self._mark_device_tags()  # 标记二极管器件、输入器件、顶层节点、共模检测器件
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
        self._register_beam_substructures()
        self._register_lv_mirror_pairs()

        # 2. 登记低压电流镜
        self._register_lv_mirrors()

        # 3. 登记普通电流镜
        self._register_current_mirrors()

        # 4. 登记 RC 子结构
        self._register_rc_structures()

        # 5. 登记对称电容
        self._register_sym_capacitors()

        # 6. 生成全局约束组
        self._generate_constraint_groups()

    # -------路径换成绝对路径--------
    def _normalize_linux_path(self, path: str) -> str:
        if not path:
            raise ValueError("路径不能为空字符串")
        normalized_path = path.replace("\\", "/")
        return os.path.abspath(normalized_path) if not os.path.isabs(normalized_path) else normalized_path

    def _load_terminals_from_cache(self):
        """从JSON缓存文件加载器件-端子映射"""
        if not self.terminals_cache_file:
            return
        try:
            with open(self.terminals_cache_file, 'r') as f:
                self._all_terminals_map = json.load(f)
        except Exception as e:
            raise IOError(f"无法从缓存 {self.terminals_cache_file} 读取: {e}")

    def _save_terminals_to_cache(self):
        """将器件-端子映射保存到JSON缓存文件"""
        if not self.terminals_cache_file:
            return
        try:
            with open(self.terminals_cache_file, 'w') as f:
                json.dump(self._all_terminals_map, f, indent=4, sort_keys=True)
            print(f"--- 器件连接信息已保存到 {self.terminals_cache_file} ---")
        except Exception as e:
            print(f"警告：无法将缓存写入 {self.terminals_cache_file}: {e}")

    # -------------------BOOT-------------------------

    # ----------------------读取器件连接导线、参数、建立网络-器件映射、创建Device实例--------------------------
    def _init_device_terminals(self):
        """
        - Online模式: 从pyAether读取端子, 构建_all_terminals_map, 并保存到缓存。
        - Offline模式: 跳过pyAether, _all_terminals_map已从缓存加载。
        两种模式下都会执行后半部分的 _net_device_map 和 Device 实例创建。
        """
        # 1. (Online模式) 从pyAether填充 self._all_terminals_map
        if not self._offline_mode:
            if not self._cv:  # 健壮性检查
                raise RuntimeError("pyAether (self._cv) 未初始化。无法在Online模式下运行。")

        # ---
        # 2. (Offline + Online) 使用 self._all_terminals_map 构建 net_device_map 和 Device 实例
        # ---
        if not self._all_terminals_map:
            raise ValueError("器件-端子映射表 (_all_terminals_map) 为空。无法继续。")

        for device_name, device_type in self.device_types.items():
            terminals = self._all_terminals_map.get(device_name)
            if terminals is None:
                raise KeyError(f"器件 '{device_name}' 在参数文件中有定义, 但在 (缓存/Aether) 端子映射中缺失。")

            # 构建网络-器件映射 (V2: 修复二极管连接导致的重复添加)
            unique_lower_nets = set(net.lower() for net in terminals.values())
            for net_lower in unique_lower_nets:
                self.net_device_map[net_lower].append(device_name)

            # 创建基础Device实例
            self.circuit.devices[device_name] = Device(
                name=device_name,
                type=device_type,
                terminals=terminals,
                params=self._get_valid_device_params(device_name, device_type)
            )

        # ---
        # 3. (Online模式) 循环结束后, 保存到缓存
        # ---
        if not self._offline_mode and self.terminals_cache_file:
            self._save_terminals_to_cache()

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
        return self._net_matches(net, self.power_positive) or self._net_matches(net, self.power_negative)

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
            dev = self.circuit.devices.get(name)
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
    def _is_top_node(self, device: Device) -> bool:
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
    ##################所有约束规则的表达可以优化，具体约束格式没有统一，且没有得到利用，没有真正让参数数量缩减###################
    #############可能存在重复约束问题
    def _register_substructure_types(self):
        """注册子结构类型及约束规则"""

        def sym_pair_constraint(members: List[Device]) -> List[str]:
            """对称对约束：差分输入对、输出对、共模检测对、对称对（栅极接对称电流支路）、低压电流镜处于同一电流支路的两个镜像管
            fw/l/m需相同
            """
            if len(members) != 2:
                return list("")

            base_constraints = [  # 正常约束
                f"{members[0].name}.fw = {members[1].name}.fw",
                f"{members[0].name}.l = {members[1].name}.l",
                f"{members[0].name}.m = {members[1].name}.m"
            ]
            return base_constraints

        def low_voltage_mirror_constraint(members: List[Device]) -> List[str]:
            """
                所有管子的约束向下层参考管看齐
            """
            try:
                # 1. 查找关键器件
                # 低压结构中的上层MOS
                upper_trans = [d for d in members if DeviceTags.LV_MIRROR_UPPER in d.tags or (
                        DeviceTags.LV_MIRROR_UPPER_REF in d.tags and DeviceTags.DIODE_MOS not in d.tags)][0]
                # 下层参考管
                lower_ref = [d for d in members if DeviceTags.LV_MIRROR_LOWER_REF in d.tags][0]
                # 真正的上层参考管 (可能是上层MOS管自己，也可能是耦合进来的二极管)
                true_upper_ref = [d for d in members if DeviceTags.LV_MIRROR_UPPER_REF in d.tags][0]
                print(upper_trans.name)
                print(true_upper_ref.name)

                # 查找所有镜像管
                upper_mirrors = [d for d in members if DeviceTags.LV_MIRROR_UPPER_MIRROR in d.tags]
                lower_mirrors = [d for d in members if DeviceTags.LV_MIRROR_LOWER_MIRROR in d.tags]

                constraints = []

                # 上层管 与 lower_ref 的 fw/l/m 必须相同
                constraints.extend([
                    f"{upper_trans.name}.fw = {lower_ref.name}.fw",
                    f"{upper_trans.name}.l = {lower_ref.name}.l",
                    f"{upper_trans.name}.m = {lower_ref.name}.m"
                ])

                # 情况1下，二极管 的 fw/l 必须与 lower_ref 相同
                # 情况1下，当上层管具有偏置镜像管的标签时，上层管的m要和二极管一样，等效为二极管的m和下层参考管一样
                if upper_trans.name != true_upper_ref.name:
                    # 检查 upper_trans 是否在 upper_mirrors 列表中
                    if upper_trans in upper_mirrors:
                        upper_mirrors.remove(upper_trans)

                    constraints.extend([
                        f"{true_upper_ref.name}.l = {lower_ref.name}.l"
                    ])
                    if DeviceTags.LV_MIRROR_BIAS_MIRROR in upper_trans.tags:
                        constraints.extend([f"{true_upper_ref.name}.m = {lower_ref.name}.m",
                            f"{true_upper_ref.name}.fw = {lower_ref.name}.fw"
                        ])

                # 上层镜像管中除去可能存在的上层管(在上一条约束中实现，因为上层管已经被约束过了)，其他管子的 fw/l 必须与 lower_ref 相同 (m可不同)
                for m in upper_mirrors:
                    base = [ f"{m.name}.l = {lower_ref.name}.l"]
                    if DeviceTags.LV_MIRROR_BIAS_MIRROR in m.tags:
                        base.extend([f"{m.name}.m = {lower_ref.name}.m",f"{m.name}.fw = {lower_ref.name}.fw"])
                    constraints.extend(base)

                # 下层镜像管的 fw/l 必须与 lower_ref 相同 (m可不同)
                for m in lower_mirrors:
                    base = [f"{m.name}.l = {lower_ref.name}.l"]
                    if DeviceTags.LV_MIRROR_BIAS_MIRROR in m.tags:
                        base.extend([f"{m.name}.m = {lower_ref.name}.m", f"{m.name}.fw = {lower_ref.name}.fw"])
                    constraints.extend(base)

                return constraints

            except IndexError:
                # 查找器件失败
                return ["# 错误：低压电流镜成员不完整，无法生成约束"]

        def cascode_constraint(members: List[Device]) -> List[str]:
            """级联约束：
            l/fw/m均相同
            """
            main = [d for d in members if DeviceTags.CASCODE_MAIN in d.tags][0]
            slaves = [d for d in members if DeviceTags.CASCODE_SLAVE in d.tags]
            constraints = []
            for s in slaves:
                base = [f"{s.name}.l = {main.name}.l", f"{s.name}.fw = {main.name}.fw", f"{s.name}.m = {main.name}.m"]
                constraints.extend(base)
            return constraints

        def load_constraint(members: List[Device]) -> List[str]:
            """负载约束：A型负载、B型负载、典型负载（2器件与4器件负载）
            l/fw/M均相同
            """
            # if len(members)!=2:
            #     return list("")
            length = len(members)
            base_constraints = []

            if length > 0:  # 健壮性检查
                ref_name = members[length - 1].name
                for i in range(length-1):
                    dev_name = members[i].name
                    base_constraints.extend([
                        f"{dev_name}.fw = {ref_name}.fw",
                        f"{dev_name}.l = {ref_name}.l",
                        f"{dev_name}.m = {ref_name}.m"
                    ])
            return base_constraints

        def current_mirror_constraint(members: List[Device]) -> List[str]:
            """
            普通电流镜约束:
            - fw/l 始终约束
            - Bias mirrors (有BIAS标签):
                - If Ref is ROOT_REF: m 相互约束, 但独立于 Ref
                - If Ref is not ROOT_REF: m 约束为等于 Ref.m
            """
            try:
                ref = [d for d in members if DeviceTags.CURRENT_MIRROR_REF in d.tags][0]
            except IndexError:
                return ["# 错误：普通电流镜缺少参考管"]

            mirrors = [d for d in members if DeviceTags.CURRENT_MIRROR_MIRROR in d.tags]
            constraints = []

            is_ref_root = DeviceTags.ROOT_REF in ref.tags

            bias_mirror_names = []  # 用于 Root Ref 的 m 相互约束

            for m in mirrors:
                is_bias_mirror = DeviceTags.CURRENT_MIRROR_BIAS_MIRROR in m.tags

                # 1. fw/l 约束 (始终应用)
                base = [f"{m.name}.l = {ref.name}.l"]

                # 2. m 约束
                if is_bias_mirror:
                    if is_ref_root:
                        # (Case 1): Ref是Root. m 独立于 ref.
                        bias_mirror_names.append(m.name)
                    else:
                        # (Case 3): Ref非Root. m = ref.m
                        base.extend([f"{m.name}.m = {ref.name}.m",f"{m.name}.fw = {ref.name}.fw"])

                constraints.extend(base)

            # 3. 添加 Case 1 (Root Ref) 的 m 相互约束
            if is_ref_root and len(bias_mirror_names) > 1:
                first_m = bias_mirror_names[0]
                for other_m in bias_mirror_names[1:]:
                    constraints.extend([f"{other_m}.m = {first_m}.m",f"{other_m}.fw = {first_m}.fw"])

            return constraints

        def common_detect_b_constraint(members: List[Device]) -> List[str]:
            """共模检测B约束：
            fw/l/m需相同
            """
            base_constraints = [  # 正常约束
                f"{members[0].name}.fw = {members[3].name}.fw",
                f"{members[0].name}.l = {members[3].name}.l",
                f"{members[0].name}.m = {members[3].name}.m",
                f"{members[1].name}.fw = {members[3].name}.fw",
                f"{members[1].name}.l = {members[3].name}.l",
                f"{members[1].name}.m = {members[3].name}.m",
                f"{members[2].name}.fw = {members[3].name}.fw",
                f"{members[2].name}.l = {members[3].name}.l",
                f"{members[2].name}.m = {members[3].name}.m"
            ]
            return base_constraints

        def _rc_constraint_helper(members: List[Device]) -> List[str]:
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
                        constraints.append(f"{res.name}.segW = {ref_res.name}.segW")
                    if has_segL:
                        constraints.append(f"{res.name}.segL = {ref_res.name}.segL")

            # 约束电容 (l)
            if len(capacitors) > 1:
                ref_cap = capacitors[0]

                # 检查参考电容是否具有 'l' 参数
                if "l" in ref_cap.params:
                    for cap in capacitors[1:]:
                        constraints.append(f"{cap.name}.l = {ref_cap.name}.l")

            return constraints

        def compensate_constraint(members: List[Device]) -> List[str]:
            """频率补偿约束 (R同, C同)"""
            return _rc_constraint_helper(members)

        def common_detect_a_constraint(members: List[Device]) -> List[str]:
            """共模检测A约束 (R同, C同)"""
            return _rc_constraint_helper(members)

        def sym_capacitor_constraint(members: List[Device]) -> List[str]:
            """对称电容约束 (l同)"""
            constraints = []
            capacitors = [d for d in members if d.type == "Capacitor"]

            if len(capacitors) > 1:
                ref_cap = capacitors[0]
                # 检查参考电容是否具有 'l' 参数
                if "l" in ref_cap.params:
                    for cap in capacitors[1:]:
                        constraints.append(f"{cap.name}.l = {ref_cap.name}.l")
            return constraints

        #---------------------------------------子结构注册---------------------------------------------
        self.circuit.substructure_types = {
            "差分输入对": SubStructureType(
                type_name="差分输入对",
                required_roles={DeviceTags.DIFF_POSITIVE, DeviceTags.DIFF_NEGATIVE},
                constraint_rules=sym_pair_constraint,
                aggregation_rule=lambda roles: lambda
                    roles: DeviceTags.DIFF_POSITIVE in roles and DeviceTags.DIFF_NEGATIVE in roles
            ),
            "输出对": SubStructureType(
                type_name="输出对",
                required_roles={DeviceTags.OUTPUT_NEGATIVE, DeviceTags.OUTPUT_POSITIVE},
                constraint_rules=sym_pair_constraint,
                aggregation_rule=lambda roles: lambda
                    roles: DeviceTags.OUTPUT_NEGATIVE and DeviceTags.OUTPUT_POSITIVE in roles
            ),
            "对称对": SubStructureType(
                type_name="对称对",
                required_roles={DeviceTags.SYM_PAIR, DeviceTags.COMMON_GET, DeviceTags.LV_MIRROR_PAIR},
                constraint_rules=sym_pair_constraint,
                aggregation_rule=lambda roles: lambda roles: DeviceTags.SYM_PAIR or DeviceTags.COMMON_GET
                        or DeviceTags.LV_MIRROR_PAIR in roles
            ),
            "低压电流镜": SubStructureType(
                type_name="低压电流镜",
                required_roles={
                    DeviceTags.LV_MIRROR_LOWER_REF,
                    DeviceTags.LV_MIRROR_LOWER_MIRROR,
                    DeviceTags.LV_MIRROR_UPPER_MIRROR,
                    DeviceTags.LV_MIRROR_UPPER_REF
                },
                constraint_rules=low_voltage_mirror_constraint,
                aggregation_rule=lambda roles: all(r in roles for r in [
                    DeviceTags.LV_MIRROR_LOWER_REF,
                    DeviceTags.LV_MIRROR_LOWER_MIRROR,
                    DeviceTags.LV_MIRROR_UPPER_MIRROR,
                    DeviceTags.LV_MIRROR_UPPER_REF
                ])
            ),
            "级联": SubStructureType(
                type_name="级联",
                required_roles={DeviceTags.CASCODE_MAIN, DeviceTags.CASCODE_SLAVE},
                constraint_rules=cascode_constraint,
                aggregation_rule=lambda roles: DeviceTags.CASCODE_MAIN in roles and DeviceTags.CASCODE_SLAVE in roles
            ),
            "普通电流镜": SubStructureType(
                type_name="普通电流镜",
                required_roles={DeviceTags.CURRENT_MIRROR_REF, DeviceTags.CURRENT_MIRROR_MIRROR},
                constraint_rules=current_mirror_constraint,
                aggregation_rule=lambda
                    roles: DeviceTags.CURRENT_MIRROR_REF in roles and DeviceTags.CURRENT_MIRROR_MIRROR in roles
            ),
            "A型负载": SubStructureType(
                type_name="A型负载",
                required_roles={DeviceTags.SPEC_A_LOAD_DIO, DeviceTags.SPEC_A_LOAD_TYP},
                constraint_rules=load_constraint,
                aggregation_rule=lambda roles: DeviceTags.SPEC_A_LOAD_TYP and DeviceTags.SPEC_A_LOAD_DIO in roles
            ),
            "B型负载": SubStructureType(
                type_name="B型负载",
                required_roles={DeviceTags.SPEC_B_LOAD},
                constraint_rules=load_constraint,
                aggregation_rule=lambda roles: DeviceTags.SPEC_B_LOAD in roles
            ),
            "典型负载": SubStructureType(
                type_name="典型负载",
                required_roles={DeviceTags.TYPICAL_LOAD},
                constraint_rules=load_constraint,
                aggregation_rule=lambda roles: DeviceTags.TYPICAL_LOAD in roles
            ),
            "共模检测B": SubStructureType(
                type_name="共模检测B",
                required_roles={DeviceTags.COMMON_OUT, DeviceTags.COMMON_GET},
                constraint_rules=common_detect_b_constraint,
                aggregation_rule=lambda roles: DeviceTags.COMMON_OUT and DeviceTags.COMMON_GET in roles
            ),
            "频率补偿": SubStructureType(
                type_name="频率补偿",
                required_roles={DeviceTags.COMPENSATE},
                constraint_rules=compensate_constraint,
                aggregation_rule=lambda roles: DeviceTags.COMPENSATE in roles
            ),
            "共模检测A": SubStructureType(
                type_name="共模检测A",
                required_roles={DeviceTags.COMMON_DETECT_A},
                constraint_rules=common_detect_a_constraint,
                aggregation_rule=lambda roles: DeviceTags.COMMON_DETECT_A in roles
            ),
            "对称电容": SubStructureType(
                type_name="对称电容",
                required_roles={DeviceTags.SYM_CAPACITOR},
                constraint_rules=sym_capacitor_constraint,
                aggregation_rule=lambda roles: DeviceTags.SYM_CAPACITOR in roles
            )
        }

    # -------------------------------------------------------特殊器件检测------------------------------------------------------------
    def _mark_device_tags(self):
        for device in self.circuit.devices.values():
            # ---------------------检测二极管连接MOS管------------------
            if device.type in ["PMOS", "NMOS"]:
                g_net = device.terminals.get("G")
                d_net = device.terminals.get("D")
                if g_net and d_net and self._net_matches(g_net, {d_net}):
                    device.tags.add(DeviceTags.DIODE_MOS)

            # -----------------------识别顶层节点-------------------------
            if self._is_top_node(device):
                self.top_nodes.append(device)

            # ------------------------标记差分输入管--------------------------
            if device.type in ["PMOS", "NMOS"]:
                g_net = device.terminals.get("G")
                if g_net:
                    if self._net_matches(g_net, self.input_positive):
                        device.tags.add(DeviceTags.DIFF_POSITIVE)
                        self.diff_pair_positive.append(device.name)
                    elif self._net_matches(g_net, self.input_negative):
                        device.tags.add(DeviceTags.DIFF_NEGATIVE)
                        self.diff_pair_negative.append(device.name)

            # ---------------------------------标记共模检测管---------------------------------
            if device.type in ["PMOS", "NMOS"]:
                g_net = device.terminals.get("G")
                if self._net_matches(g_net, self.common_sign):
                    device.tags.add(DeviceTags.COMMON_GET)
                    self.common_get.append(device.name)

    # ------------------------------------------------ 标记输出管/频率补偿/共模检测A --------------------------------------------------------
    def _mark_output_devices(self):
        """
        使用 net_device_map 快速标记输出管 (MOS)，
        根据预定义逻辑检测连接到输出端的 RC 结构，应用时应检查预定义逻辑是否匹配电路设计。
        """

        # --- 辅助函数 1: 获取二端器件的另一端网络(在电流路径中存在重合函数，可以优化) ---
        def _get_other_terminal_net(device: Device, connected_net: str) -> Optional[str]:
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

                dev = self.circuit.devices.get(dev_name)
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
        def _get_net_single_resistor(net: str, exclude_devices: Set[str]) -> Optional[Device]:
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
                dev = self.circuit.devices.get(dev_name)
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
                device = self.circuit.devices.get(dev_name)
                if not device:
                    continue

                # --- 规则 0: 标记 MOS 输出管 ---
                if device.type in ["PMOS", "NMOS"]:
                    if net_name.lower() in positive_nets_lower:
                        if DeviceTags.OUTPUT_POSITIVE not in device.tags and (
                                self._net_matches(device.terminals.get("S"), {net_name}) or self._net_matches(
                                device.terminals.get("D"), {net_name})):
                            device.tags.add(DeviceTags.OUTPUT_POSITIVE)
                            self.positive_output.append(dev_name)
                    elif net_name.lower() in negative_nets_lower:
                        if DeviceTags.OUTPUT_NEGATIVE not in device.tags and (
                                self._net_matches(device.terminals.get("S"), {net_name}) or self._net_matches(
                                device.terminals.get("D"), {net_name})):
                            device.tags.add(DeviceTags.OUTPUT_NEGATIVE)
                            self.negative_output.append(dev_name)

                # --- 规则 1: 器件是电容 ---
                elif device.type == "Capacitor":
                    cap_device = device
                    other_net = _get_other_terminal_net(cap_device, net_name)   #输出端网络的另一端
                    if not other_net:
                        continue

                    exclude_set = {cap_device.name}
                    mos_conns = _get_net_mos_connections(other_net, exclude_set)
                    num_mos = len(mos_conns)

                    if num_mos > 1:
                        # Case C1 (多MOS): 标记 COMPENSATE
                        cap_device.tags.add(DeviceTags.COMPENSATE)
                        self.compensate.append(cap_device.name)

                    elif num_mos == 1:
                        if mos_conns[0]['conn_type'] == 'G':
                            # Case C2.1 (单MOS 栅极): 标记 COMMON_DETECT_A
                            cap_device.tags.add(DeviceTags.COMMON_DETECT_A)
                            self.common_detect_a.append(cap_device.name)
                        else:
                            # Case C2.2 (单MOS S/D): 标记 COMPENSATE
                            cap_device.tags.add(DeviceTags.COMPENSATE)
                            self.compensate.append(cap_device.name)

                    elif num_mos == 0:
                        # Case C3 (无MOS, 检查串联电阻)
                        serial_res = _get_net_single_resistor(other_net, exclude_set)
                        if serial_res:
                            # 确实是 C -> R 结构
                            far_net = _get_other_terminal_net(serial_res, other_net)    #电阻未与电容相连的那一端
                            if not far_net:
                                continue

                            exclude_set_far = {cap_device.name, serial_res.name}
                            mos_conns_far = _get_net_mos_connections(far_net, exclude_set_far)
                            num_mos_far = len(mos_conns_far)

                            if num_mos_far > 1:
                                # Case C3.1 (C->R->多MOS): 标记 COMPENSATE
                                cap_device.tags.add(DeviceTags.COMPENSATE)
                                serial_res.tags.add(DeviceTags.COMPENSATE)
                                self.compensate.append(cap_device.name)
                                self.compensate.append(serial_res.name)

                            elif num_mos_far == 1:
                                if mos_conns_far[0]['conn_type'] == 'G':
                                    # Case C3.2.1 (C->R->单MOS 栅极): 跳过
                                    pass
                                else:
                                    # Case C3.2.2 (C->R->单MOS S/D): 标记 COMPENSATE
                                    cap_device.tags.add(DeviceTags.COMPENSATE)
                                    serial_res.tags.add(DeviceTags.COMPENSATE)
                                    self.compensate.append(cap_device.name)
                                    self.compensate.append(serial_res.name)
                        # else:
                        # Case C4 (无MOS, 也非单个电阻): 跳过

                # --- 规则 2: 器件是电阻 ---
                elif device.type == "Resistor":
                    res1_device = device
                    other_net = _get_other_terminal_net(res1_device, net_name)  #未与输出端相连的那一端
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
                            res1_device.tags.add(DeviceTags.COMMON_DETECT_A)
                            self.common_detect_a.append(res1_device.name)
                        # else:
                        # Case R2.2 (单MOS S/D): 跳过

                    elif num_mos == 0:
                        # Case R3 (无MOS, 检查串联电阻)
                        serial_res2 = _get_net_single_resistor(other_net, exclude_set)
                        if serial_res2:
                            # 确实是 R1 -> R2 结构
                            far_net = _get_other_terminal_net(serial_res2, other_net)   #R2中未与R1电阻相连的那一端
                            if not far_net:
                                continue

                            exclude_set_far = {res1_device.name, serial_res2.name}
                            mos_conns_far = _get_net_mos_connections(far_net, exclude_set_far)
                            num_mos_far = len(mos_conns_far)

                            if num_mos_far == 1:
                                if mos_conns_far[0]['conn_type'] == 'G':
                                    # Case R3.2.1 (R1->R2->单MOS 栅极): 标记两者 COMMON_DETECT_A
                                    res1_device.tags.add(DeviceTags.COMMON_DETECT_A)
                                    serial_res2.tags.add(DeviceTags.COMMON_DETECT_A)
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
            dev1 = self.circuit.devices[self.common_get[0]]
            dev2 = self.circuit.devices[self.common_get[1]]

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
                dev = self.circuit.devices.get(name)
                if dev and dev.type in ["PMOS", "NMOS"] and self._net_matches(dev.terminals.get("S"), {common_s_net}):
                    other_mos_devices.append(dev)

            # 检查是否 *恰好* 连接另外两个MOS管
            if len(other_mos_devices) == 2:
                all_four_devices = [dev1, dev2] + other_mos_devices

                # 标记输出管
                other_mos_devices[0].tags.add(DeviceTags.COMMON_OUT)
                other_mos_devices[1].tags.add(DeviceTags.COMMON_OUT)
                self.common_detect_b = [dev1.name, dev2.name, other_mos_devices[0].name, other_mos_devices[1].name]
                # 标记整体结构
                for dev in all_four_devices:
                    dev.tags.add(DeviceTags.COMMON_DETECT_B)
                # print(f"信息：识别到B型共模检测结构，成员: {[d.name for d in all_four_devices]}")

        except KeyError:
            print("器件名称不在 self.circuit.devices 中，忽略")
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
            device for device in self.circuit.devices.values()
            if DeviceTags.DIODE_MOS in device.tags
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

                device = self.circuit.devices.get(name)

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
            found.tags.add(DeviceTags.CASCODE_SLAVE)
            cascode_slaves.append(found)
            current_s_net = found.terminals.get("S")
            slaves.remove(found)

        if cascode_slaves:
            master.tags.add(DeviceTags.CASCODE_MAIN)
            slave_names = [s.name for s in cascode_slaves]
            self.cascode_cache[master.name] = slave_names
            # 我们默认电流束中不会出现级联子结构，且不会与其他子结构重合，所以在器件标记这一部分就直接登记级联子结构
            self.aggregate_substructure("级联", [master] + cascode_slaves, f"cascode_{master.name}")

    def _mark_current_mirror_roles(self, group: Dict):
        master = group["master"]
        remaining_slaves = [s for s in group["slaves"] if DeviceTags.CASCODE_SLAVE not in s.tags]  # 这里要是没if就错了
        if not remaining_slaves:
            return
        master.tags.add(DeviceTags.CURRENT_MIRROR_REF)
        for slave in remaining_slaves:
            slave.tags.add(DeviceTags.CURRENT_MIRROR_MIRROR)

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
            #return  # 未找到起始网络，正常退出

        # 2. 查找起始器件
        # 路径的起始点必须是唯一的二极管连接的参考管
        start_candidates = []
        for dev_name in start_net_device_names:
            dev = self.circuit.devices.get(dev_name)
            if dev and (DeviceTags.DIODE_MOS in dev.tags and
                        DeviceTags.CURRENT_MIRROR_REF in dev.tags):
                start_candidates.append(dev)

        # 根据约束，这条路径的起点必须是唯一的
        if len(start_candidates) != 1:
            raise ValueError(f"警告：电流源网络 '{start_net}' 未找到或找到多个 (>=1) 根参考管。")

        current_device = start_candidates[0]

        # 3. 循环遍历路径，直到负电源
        while current_device:
            # 检查约束 (理论上已在查找时满足，但双重检查)
            if not (DeviceTags.DIODE_MOS in current_device.tags and
                    DeviceTags.CURRENT_MIRROR_REF in current_device.tags):
                break  # 路径中断，不满足约束

            # 标记为根参考管
            current_device.tags.add(DeviceTags.ROOT_REF)

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

                dev = self.circuit.devices.get(dev_name)
                # 路径上的下一个器件也必须是二极管连接的参考管
                if dev and (DeviceTags.DIODE_MOS in dev.tags and
                            DeviceTags.CURRENT_MIRROR_REF in dev.tags):
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
        mos_devices = [d for d in self.circuit.devices.values() if d.type in ["PMOS", "NMOS"]]
        processed_mos = set()

        # 预构建栅极网络,MOS管映射
        gate_net_map: DefaultDict[str, Set[Device]] = defaultdict(set)
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
                b = self.circuit.devices.get(b_name)
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
                    a.tags.add(
                        DeviceTags.LV_MIRROR_UPPER_REF if DeviceTags.CURRENT_MIRROR_MIRROR not in a.tags else DeviceTags.LV_MIRROR_UPPER)
                    b.tags.add(DeviceTags.LV_MIRROR_LOWER_REF)
                    processed_mos.add(a_name)
                    processed_mos.add(b_name)
                    self._mark_low_voltage_mirrors(a, b, gate_net_map)  # 传入预构建的映射
                    break

                # 情况2：B的D连A的G，B的S连A的D
                if self._net_matches(b_d, {a_g}) and self._net_matches(b_s, {a_d}) and not self._net_matches(b_g,
                                                                                                             {a_g}):
                    b.tags.add(
                        DeviceTags.LV_MIRROR_UPPER_REF if DeviceTags.CURRENT_MIRROR_MIRROR not in b.tags else DeviceTags.LV_MIRROR_UPPER)
                    a.tags.add(DeviceTags.LV_MIRROR_LOWER_REF)
                    processed_mos.add(a_name)
                    processed_mos.add(b_name)
                    self._mark_low_voltage_mirrors(b, a, gate_net_map)  # 传入预构建的映射
                    break

    #################################################低压电流镜标记######################################################
    ##################################################################################################################
    def _mark_low_voltage_mirrors(self, upper_transis: Device, lower_ref: Device, gate_net_map):
        """标记低压电流镜的镜像管"""
        upper_trans_g = upper_transis.terminals["G"]
        lower_ref_g = lower_ref.terminals["G"]

        true_upper_ref = None
        upper_mirrors_list = []

        # 情况 (1): "耦合" 上层管是镜像管
        if DeviceTags.LV_MIRROR_UPPER in upper_transis.tags:
            # 查找与上层管在同一栅极的二极管 (即真正的上层参考管)
            devices_on_gate = gate_net_map.get(upper_trans_g.lower(), set())
            diode_mos_list = [d for d in devices_on_gate if DeviceTags.DIODE_MOS in d.tags]

            if diode_mos_list:
                true_upper_ref = diode_mos_list[0]
                true_upper_ref.tags.add(DeviceTags.LV_MIRROR_UPPER_REF)  # 赋予新标签
            else:
                # 严重错误：逻辑上层管 应该是某个二极管的镜像管，但没找到
                print(f"警告：LV结构 {upper_transis.name} 缺少二极管参考管，无法登记。")
                return
        # 情况 (2): "独立" 上层管是参考管
        elif DeviceTags.LV_MIRROR_UPPER_REF in upper_transis.tags:
            true_upper_ref = upper_transis
        else:
            return  # 异常情况

        # 3. 标记上层镜像管 (基于 true_upper_ref)
        true_upper_ref_g = true_upper_ref.terminals["G"]
        all_upper_devices_on_gate = gate_net_map.get(true_upper_ref_g.lower(), set())

        for mos in all_upper_devices_on_gate:
            # 排除真正的参考管
            if mos.name == true_upper_ref.name:
                continue

            # 上层管(upper_trans)也会在这里被标记 (如果它不是true_upper_ref)
            mos.tags.add(DeviceTags.LV_MIRROR_UPPER_MIRROR)
            upper_mirrors_list.append(mos)

        # 4. 标记下层镜像管 (基于 lower_ref)
        all_lower_devices_on_gate = gate_net_map.get(lower_ref_g.lower(), set())
        lower_mirrors_list = []

        for mos in all_lower_devices_on_gate:
            if mos.name == lower_ref.name:
                continue

            mos.tags.add(DeviceTags.LV_MIRROR_LOWER_MIRROR)
            lower_mirrors_list.append(mos)

        if upper_mirrors_list and lower_mirrors_list:  # 上下都一定要有镜像管
            # 收集所有镜像管的名称
            all_mirror_names = [m.name for m in upper_mirrors_list] + \
                               [m.name for m in lower_mirrors_list]

            if DeviceTags.LV_MIRROR_UPPER in upper_transis.tags:  #

                # 检查这个耦合结构是否在普通电流镜缓存中
                if true_upper_ref.name in self.current_cache:
                    print(f"  [净化]: 检测到LV耦合，正在净化 {true_upper_ref.name} 及其普通电流镜...")

                    # 1. 获取所有被错误标记的镜像管
                    mirror_names_to_clean = self.current_cache[true_upper_ref.name]

                    # 2. (关键) 清除所有镜像管的陈旧标签
                    for name in mirror_names_to_clean:
                        if name in self.circuit.devices:
                            self.circuit.devices[name].tags.discard(DeviceTags.CURRENT_MIRROR_MIRROR)

                    # 3. (关键) 清除参考管的陈旧标签
                    true_upper_ref.tags.discard(DeviceTags.CURRENT_MIRROR_REF)
                    #true_upper_ref.tags.discard(DeviceTags.DIODE_MOS)  # 也可能是二极管

                    # 4. (关键) 清除缓存
                    del self.current_cache[true_upper_ref.name]

                # 构建值列表: [true_upper_ref_name, mirror1, mirror2, ...]
                value_list = [true_upper_ref.name] + all_mirror_names
            else:
                # "独立"情况
                # 去除 true_upper_ref 自身名后再构建列表，保证格式统一
                mirrors_excluding_ref = [n for n in all_mirror_names if n != true_upper_ref.name]
                value_list = [true_upper_ref.name] + mirrors_excluding_ref

            self.lv_current[lower_ref.name] = value_list

    # -----------------------------------------------------电流路径生成-----------------------------------------------------------
    def generate_current_paths(self):
        """优化电阻基准网络计算，统一子节点与父节点的连接网络"""
        all_paths: List[List[str]] = []

        # ------------------------------
        # 通用辅助函数
        # ------------------------------
        def get_terminals(device: Device) -> Dict[str, str]:
            """获取器件有效端子-网络映射（源漏/正负端）"""
            if device.type in ["PMOS", "NMOS"]:
                return {k: v for k, v in device.terminals.items() if k in ["S", "D"]}
            elif device.type == "Resistor":
                return {k: v for k, v in device.terminals.items() if k in ["PLUS", "MINUS"]}
            return {}

        def get_other_net(device: Device, known_net: str) -> str:
            """获取器件中与已知网络不同的另一端网络"""
            nets = list(get_terminals(device).values())
            # 健壮性检查，防止 nets 列表为空或长度不足
            if len(nets) < 2:
                return ""
            return nets[0] if nets[1] == known_net else nets[1] if nets[0] == known_net else ""

        def get_res_other_net(device: Device, target_set: Set[str]) -> str:
            """获取电阻非电源的一端网络"""
            if not device:
                return ""
            target_lower = {s.lower() for s in target_set}
            term_nets = list(get_terminals(device).values())
            if len(term_nets) < 2:
                return ""
            (net1, net2) = term_nets
            return net1 if net2.lower() in target_lower else net2 if net1.lower() in target_lower else ""

            # ------------------------------

        # 子节点扩展核心逻辑（包含电阻基准网络）
        # ------------------------------
        def find_children(current: Device, parent_net: str = None) -> List[Device]:
            current_type = current.type
            terminals = get_terminals(current)
            children: List[Device] = []

            if current_type == "NMOS":
                # 基准网络：NMOS的源极（S）
                s_net = terminals.get("S")
                if not s_net:
                    return []

                # 子节点：漏极接S的其他NMOS
                children.extend([
                    d for d in self.circuit.devices.values()
                    if d.type == "NMOS" and d.name != current.name and d.terminals.get("D") == s_net
                ])

                # 子节点：一端接S且另一端符合条件的电阻（中间电阻）
                for res in [d for d in self.circuit.devices.values() if
                            d.type == "Resistor" and d.name != current.name]:
                    res_nets = get_terminals(res).values()
                    if s_net not in res_nets:
                        continue
                    other_net = get_other_net(res, s_net)
                    if not other_net:
                        continue

                    valid = (self._net_matches(other_net, self.power_negative)) or any(
                        (d.type == "NMOS" and d.terminals.get("D") == other_net)
                        for d in self.circuit.devices.values() if d.name != res.name
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
                    d for d in self.circuit.devices.values()
                    if d.name != current.name and (
                            (d.type == "NMOS" and d.terminals.get("D") == d_net) or
                            (d.type == "PMOS" and d.terminals.get("S") == d_net)
                    )
                ])

                # 子节点：一端接D且另一端符合条件的电阻（中间电阻）
                for res in [d for d in self.circuit.devices.values() if
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
                        for d in self.circuit.devices.values() if d.name != res.name
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
                    d for d in self.circuit.devices.values()
                    if d.name != current.name and (
                            (d.type == "NMOS" and d.terminals.get("D") == base_net) or
                            (d.type == "PMOS" and d.terminals.get("S") == base_net)
                    )
                ])

            return children

        # ------------------------------
        # 路径终止判断
        # ------------------------------
        def _is_path_terminated(device: Device) -> bool:
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
        def dfs(current: Device, path: List[str], parent_net: str = None):
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
                # ---将内部网络添加到路径中 ---
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
                path_devs = path[::2]
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
                path_devs = path[::2]
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
                path_devs = path[::2]
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
            device = self.circuit.devices.get(dev_name)
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
                path_device_set = set(path[::2])
                # 检查路径器件集合 与 目标器件集合 是否有交集
                if not path_device_set.isdisjoint(devices_on_out_g_nets):
                    beam3_candidates.add(path)

        # 3d. 将这些候选路径按长度分组
        grouped_by_length_beam3: DefaultDict[int, List[List[str]]] = defaultdict(list)
        for path in beam3_candidates:
            grouped_by_length_beam3[len(path[::2])].append(list(path))

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
            remaining_grouped_by_length[len(path_tuple[::2])].append(path_tuple)

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

                    path_i_devs = paths[i][::2]
                    path_j_devs = paths[j][::2]

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

        # --- 提取内部网络 ---
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
                path_devs = p[::2]
                if len(path_devs) > max_len:
                    max_len = len(path_devs)

            # 2. 按索引生成集合列表，并标记器件
            current_beam_path: List[Set[str]] = []
            for i in range(max_len):
                index_set: Set[str] = set()
                for path in paths_list:
                    path_devs = path[::2]
                    # 确保路径足够长，可以访问此索引
                    if i < len(path_devs):
                        dev_name = path_devs[i]
                        index_set.add(dev_name)
                        # --- 嵌入标签 ---
                        device = self.circuit.devices.get(dev_name)
                        if device:
                            device.tags.add(DeviceTags.IN_CURRENT_BEAM)
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
                ref_device = self.circuit.devices[ref_name]
                # Case 2: Ref 在电流束中，跳过 (不标记其
                if DeviceTags.IN_CURRENT_BEAM in ref_device.tags:
                    continue
                # Case 1 & 3: Ref 不在电流束中
                bias_mirror : List[str] = []
                for name in mirror_names_list:
                    dev = self.circuit.devices.get(name)
                    # 如果镜像管 *不* 在电流束中，则标记为 BIAS
                    if dev and DeviceTags.IN_CURRENT_BEAM not in dev.tags:
                        dev.tags.add(DeviceTags.CURRENT_MIRROR_BIAS_MIRROR)
                        bias_mirror.append(dev.name)

                if DeviceTags.ROOT_REF in ref_device.tags:
                    self.root_bias_mirror[ref_device.name] = bias_mirror
            except KeyError:
                continue  # 器件在字典中但不在 devices 中

        for lower_ref_name, value_list in self.lv_current.items():
            try:
                lower_ref_device = self.circuit.devices[lower_ref_name]

                if DeviceTags.IN_CURRENT_BEAM in lower_ref_device.tags:
                    continue
                # Case 1: 下层 Ref 不在电流束中
                mirror_names_list = value_list[1:]  # 索引0是 true_upper_ref

                for name in mirror_names_list:
                    dev = self.circuit.devices.get(name)
                    # 如果镜像管 *不* 在电流束中，则标记为 BIAS
                    if dev and DeviceTags.IN_CURRENT_BEAM not in dev.tags:
                        dev.tags.add(DeviceTags.LV_MIRROR_BIAS_MIRROR)

            except KeyError:
                continue  # 器件在字典中但不在 devices 中

    # -------------------------------------------------子结构实例检测与登记----------------------------------------------------------
    #函数识别顺序需要优化以提高代码效率
    def _register_beam_substructures(self):
        """
        遍历电流束路径中的 *所有器件对*，登记：
        1. 特殊或G-连接的对称对 (Diff, Out, Loads, Common) 并更新类属性
        2. 非G-连接的跨束对称对 (SYM_PAIR)，基于 *内部网络* 检查
        3.优先登记 4-器件 结构 (CMFB, Quad Load)(后续可优化识别顺序)
        """
        def _register_helper(members: List[Device], sub_type: str, sub_id_prefix: str):
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

        def _check_cross_beam_symmetry(mos_a: Device, mos_b: Device) -> bool:
            """
                检查两个MOS管的栅极网络是否在同一个电流束的 *内部网络* 集合中。
            """
            g_net_a = mos_a.terminals.get("G")
            g_net_b = mos_b.terminals.get("G")

            if not g_net_a or not g_net_b:
                return False

            # 遍历在 analyze_current_beams 中生成的网络集合
            for beam_net_set in self.circuit.beam_net_sets.values():
                if self._net_matches(g_net_a,beam_net_set) and self._net_matches(g_net_b,beam_net_set):
                    return True  # 匹配成功

            return False

        # --- 优化：构建镜像管 -> 参考管 的反向查找字典 ---
        mirror_to_ref_map: Dict[str, str] = {}
        # 1. 普通电流镜
        for ref_name, mirror_list in self.current_cache.items():
            for mirror_name in mirror_list:
                mirror_to_ref_map[mirror_name] = ref_name
        # 2. 低压电流镜 (所有镜像管都映射到 *同一个* 下层参考管键)
        for lower_ref_name, lv_list in self.lv_current.items():
            for mirror_name in lv_list[1:]:  # 索引0是 true_upper_ref
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
                        members = [self.circuit.devices[name] for name in element_set_names]
                    except KeyError:
                        continue  # 器件不存在

                    # 规则 1: 共模检测B
                    if all(DeviceTags.COMMON_DETECT_B in d.tags for d in members):
                        _register_helper(members, "共模检测B", "cmfb")
                        processed_4_devices.union(element_set_names)
                        continue  # 登记成功

                    # 规则 2: 典型负载 (基于栅极连接)
                    g_net_groups: DefaultDict[str, List[Device]] = defaultdict(list)
                    for d in members:
                        g_net = d.terminals.get("G")
                        if g_net:
                            g_net_groups[g_net].append(d)

                    unique_g_nets = len(g_net_groups)

                    if unique_g_nets == 1:
                        # 所有 4 个栅极相连
                        for d in members: d.tags.add(DeviceTags.TYPICAL_LOAD)
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
                            dev_a = self.circuit.devices[dev_a_name]
                            dev_b = self.circuit.devices[dev_b_name]
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
                            self.diff_pair.extend([dev_a.name,dev_b_name])
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
                        a_is_diode = DeviceTags.DIODE_MOS in dev_a.tags
                        b_is_diode = DeviceTags.DIODE_MOS in dev_b.tags
                        a_load_match = False
                        if a_is_diode and dev_b_name in self.current_cache.get(dev_a_name, []):
                            dev_a.tags.add(DeviceTags.SPEC_A_LOAD_DIO)
                            dev_b.tags.add(DeviceTags.SPEC_A_LOAD_TYP)
                            a_load_match = True
                        elif b_is_diode and dev_a_name in self.current_cache.get(dev_b_name, []):
                            dev_b.tags.add(DeviceTags.SPEC_A_LOAD_DIO)
                            dev_a.tags.add(DeviceTags.SPEC_A_LOAD_TYP)
                            a_load_match = True
                        if a_load_match:
                            self.A_load.append([dev_a_name,dev_b_name])
                            _register_helper(members, "A型负载", "a_load")
                            processed_devices.add(dev_a_name)
                            processed_devices.add(dev_b_name)
                            continue  # 登记成功

                        # 规则 4: B型负载 (两个二极管)
                        if a_is_diode and b_is_diode:
                            dev_a.tags.add(DeviceTags.SPEC_B_LOAD)
                            dev_b.tags.add(DeviceTags.SPEC_B_LOAD)
                            self.B_load.append([dev_a_name,dev_b_name])
                            _register_helper(members, "B型负载", "b_load")
                            processed_devices.add(dev_a_name)
                            processed_devices.add(dev_b_name)
                            continue  # 登记成功

                        # 规则 5: 典型负载 (来自电流镜)
                        ref_a = mirror_to_ref_map.get(dev_a_name)
                        ref_b = mirror_to_ref_map.get(dev_b_name)
                        if ref_a is not None and ref_a == ref_b:
                            dev_a.tags.add(DeviceTags.TYPICAL_LOAD)
                            dev_b.tags.add(DeviceTags.TYPICAL_LOAD)
                            self.typ_load.append([dev_a_name,dev_b_name])
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
                            dev_a.tags.add(DeviceTags.COMMON_GET)
                            dev_b.tags.add(DeviceTags.COMMON_GET)
                            _register_helper(members, "对称对", "sym_pair")
                            processed_devices.add(dev_a_name)
                            processed_devices.add(dev_b_name)
                            continue  # 登记成功

                        # --- 非 G-连接的对称对 ---
                        g_net_a = dev_a.terminals.get("G")
                        g_net_b = dev_b.terminals.get("G")
                        if g_net_a and g_net_b and g_net_a != g_net_b:
                            if _check_cross_beam_symmetry(dev_a, dev_b):
                                dev_a.tags.add(DeviceTags.SYM_PAIR)
                                dev_b.tags.add(DeviceTags.SYM_PAIR)
                                self.sym_pair.append([dev_a_name,dev_b_name])
                                _register_helper(members, "对称对", "sym_pair_cross")
                                processed_devices.add(dev_a_name)
                                processed_devices.add(dev_b_name)
                                continue  # 登记成功

    # --------------------------------------------登记低压电流镜镜像对管-------------------------------------------
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
                        dev_a = self.circuit.devices[dev_a_name]
                        dev_b = self.circuit.devices[dev_b_name]
                    except KeyError:
                        continue  # 器件不存在

                    # --- 检查核心逻辑 ---
                    # 1. 检查是否为非偏置管
                    is_bias_a = DeviceTags.LV_MIRROR_BIAS_MIRROR in dev_a.tags
                    is_bias_b = DeviceTags.LV_MIRROR_BIAS_MIRROR in dev_b.tags
                    if is_bias_a or is_bias_b:
                        continue  # 任意一个是偏置管，则跳过

                    # 2. 检查是否为 上/下 镜像对
                    is_upper_a = DeviceTags.LV_MIRROR_UPPER_MIRROR in dev_a.tags
                    is_lower_a = DeviceTags.LV_MIRROR_LOWER_MIRROR in dev_a.tags
                    is_upper_b = DeviceTags.LV_MIRROR_UPPER_MIRROR in dev_b.tags
                    is_lower_b = DeviceTags.LV_MIRROR_LOWER_MIRROR in dev_b.tags

                    is_pair_match = (is_upper_a and is_lower_b) or (is_lower_a and is_upper_b)

                    if is_pair_match:
                        # 3. 登记
                        dev_a.tags.add(DeviceTags.LV_MIRROR_PAIR)
                        dev_b.tags.add(DeviceTags.LV_MIRROR_PAIR)

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
            # value_list = [true_upper_ref_name, mirror1, mirror2, ...]
            # 完整的成员列表 = [lower_ref] + [true_upper_ref] + [mirrors]
            all_member_names = [lower_ref_name] + value_list

            # 获取 Device 对象
            all_members: List[Device] = []
            for name in all_member_names:
                device = self.circuit.devices.get(name)
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
            ref_device = self.circuit.devices.get(ref_name)
            if not ref_device:
                print(f"警告：在登记普通电流镜时未找到参考管 {ref_name}。")
                continue

            all_members: List[Device] = [ref_device]
            for name in mirror_names_list:
                device = self.circuit.devices.get(name)
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

    # ------------------------------------------登记频率补偿和共模检测A ------------------------------------------------
    def _register_rc_structures(self):
        """
        遍历 RC 缓存，登记 频率补偿 和 共模检测A 子结构。
        """
        # 1. 登记 频率补偿
        if self.compensate:
            members: List[Device] = []
            # 使用 set 确保器件唯一
            for name in set(self.compensate):
                dev = self.circuit.devices.get(name)
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
            members: List[Device] = []
            # 使用 set 确保器件唯一
            for name in set(self.common_detect_a):
                dev = self.circuit.devices.get(name)
                if dev:
                    members.append(dev)

            if members:
                self.aggregate_substructure(
                    sub_type="共模检测A",
                    members=members,
                    sub_id="common_detect_a_rc_global"
                )

    #-------------------------------------------登记对称电容-------------------------------------------
    def _register_sym_capacitors(self):
        """
            遍历所有未被分配的电容, 检查对称性。
        """
        # 1. 收集候选电容
        excluded_caps = set(self.compensate).union(set(self.common_detect_a))
        caps_to_check = [
            d for d in self.circuit.devices.values()
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
                    c1.tags.add(DeviceTags.SYM_CAPACITOR)
                    c2.tags.add(DeviceTags.SYM_CAPACITOR)
                    self.capacitor_pair.append([c1.name,c2.name])

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
    def aggregate_substructure(self, sub_type: str, members: List[Device], sub_id: str):
        """tight_cons参数控制约束松紧"""
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

        self.circuit.substructures.append(SubStructureInstance(
            sub_id=sub_id,
            type=sub_type,
            members=[d.name for d in members],
            constraints=constraints
        ))

        for device in members:
            device.substructures.append(SubStructureRef(sub_type=sub_type, sub_id=sub_id))

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

                    # 添加无向边
                    if param_a and param_b:
                        adj_list[param_a].add(param_b)
                        adj_list[param_b].add(param_a)
                except Exception:
                    # 捕获潜在的解析错误
                    print(f"警告：无法解析约束 '{constraint_str}'")
                    continue

        # 2. 获取 *所有* 可能的参数
        all_params_set: Set[str] = set()
        for device in self.circuit.devices.values():
            for param_key in device.params.keys():
                all_params_set.add(f"{device.name}.{param_key}")

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

# ------------------------------
# 使用示例
# ------------------------------
if __name__ == "__main__":
    # 定义电路和缓存文件
    lib_path = "2025_EDA_case2"
    cell_name = "OPA"
    view_name = "schematic"

    # 缓存文件将以 "2025_EDA_case1_terminals_cache.txt" 的形式保存在脚本同目录下
    cache_file = os.path.join(os.getcwd(), f"{lib_path}_terminals_cache.txt")

    param_file = os.path.join(os.getcwd(), "case2_extractcdfVal_0.txt")

    if not os.path.exists(param_file):
        raise FileNotFoundError(f"参数文件不存在：{param_file}")

    try:
        param_manager = ParameterManager(param_file)
    except Exception as e:
        traceback.print_exc()
        raise RuntimeError(f"参数管理器初始化失败：{str(e)}") from e

    try:
        analyzer = CircuitAnalyzer(
            lib=lib_path,
            cell=cell_name,
            view=view_name,
            param_manager=param_manager,
            power_positive={"VDD_1P8"},  # 自定义电源集合
            terminals_cache_file=cache_file  # 传入缓存路径
        )
    except Exception as e:
        traceback.print_exc()
        raise RuntimeError(f"分析器初始化失败：{str(e)}") from e

    # --- (新) 测试代码 ---
    print("\n" + "=" * 30 + " 测试输出 " + "=" * 30)

    # 1. 检查器件数量
    print(f"\n[电路基本信息]")
    print(f"  识别到的器件总数: {len(analyzer.circuit.devices)}")

    # 2. 检查部分器件的标签和所属子结构
    print(f"\n[部分器件详情]")
    devices_to_check = ["NM0", "PM0", "NM14", "C0"]  # 示例器件
    for name in devices_to_check:
        dev = analyzer.circuit.devices.get(name)
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
    print(f"  输出对 (output_pair): {analyzer.output_pair}\n")
    
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
    print(f"  对称对 (sym_pair): {analyzer.sym_pair}")

    print(f"\n[电流束内部网络 (Beam Net Sets)]")
    if analyzer.circuit.beam_net_sets:
        for beam_id, net_set in analyzer.circuit.beam_net_sets.items():
            print(f"  电流束: {beam_id} (包含 {len(net_set)} 个内部网络)")
            print(f"    - 网络: {net_set}") # 详细网络可选
    else:
        print("  未生成电流束内部网络。")

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

    # 7. 检查登记的子结构实例
    print("\n[登记的子结构实例]")
    if analyzer.circuit.substructures:
        for i, sub in enumerate(analyzer.circuit.substructures, 1):
            print(f"  实例 {i}:")
            print(f"    ID: {sub.sub_id}")
            print(f"    类型: {sub.type}")
            print(f"    成员: {sub.members}")
            print(f"    约束: {sub.constraints}") # 约束较长，可选打印
    else:
        print("  未登记任何子结构实例。")
    # 8.电路参数列表
    print("\n[全局约束组 (Constraint Groups)]")
    if analyzer.constraint_groups:
        print(f"  共找到 {len(analyzer.constraint_groups)} 个等效参数组 (包含独立参数)：")
        for i, group in enumerate(analyzer.constraint_groups, 1):
            print(f"  组 {i}: {group}")
    else:
        print("  未生成任何全局约束组。")

    print("\n" + "=" * 28 + " 测试输出结束 " + "=" * 28)