section \<open>WebAssembly Core AST\<close>

theory Wasm_Ast imports Main "Native_Word.Uint8" begin

type_synonym \<comment> \<open>immediate\<close>
  i = nat
type_synonym \<comment> \<open>static offset\<close>
  off = nat
type_synonym \<comment> \<open>alignment exponent\<close>
  a = nat
type_synonym \<comment> \<open>address\<close>
  addr = nat
type_synonym \<comment> \<open>timestamp\<close>
  h = nat

\<comment> \<open>primitive types\<close>
typedecl i32
typedecl i64
typedecl f32
typedecl f64

\<comment> \<open>memory\<close>
\<comment> \<open>TODO: Use mt instead of nat?\<close>
type_synonym byte = uint8

typedef bytes = "UNIV :: (byte list) set" ..
setup_lifting type_definition_bytes
declare Quotient_bytes[transfer_rule]

lift_definition bytes_takefill :: "byte \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> bytes" is "(\<lambda>a n as. takefill (Abs_uint8 a) n as)" .
lift_definition bytes_replicate :: "nat \<Rightarrow> byte \<Rightarrow> bytes" is "(\<lambda>n b. replicate n (Abs_uint8 b))" .
definition msbyte :: "bytes \<Rightarrow> byte" where
  "msbyte bs = last (Rep_bytes bs)"

typedef mem = "UNIV :: (byte list) set" ..
setup_lifting type_definition_mem
declare Quotient_mem[transfer_rule]

lift_definition read_bytes :: "mem \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bytes" is "(\<lambda>m n l. take l (drop n m))" .
lift_definition write_bytes :: "mem \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> mem" is "(\<lambda>m n bs. (take n m) @ bs @ (drop (n + length bs) m))" .
lift_definition mem_append :: "mem \<Rightarrow> bytes \<Rightarrow> mem" is append .

\<comment> \<open>host\<close>
typedecl host
typedecl host_state

datatype
  sh = T_loc | T_sh

datatype
  ord = Unord | Seqcst

datatype
  tr = Anyref | Funcref

record rt = \<comment> \<open>reference types\<close>
  rt_sh :: sh
  rt_tr :: tr

datatype \<comment> \<open>numeric types\<close>
  nt = T_i32 | T_i64 | T_f32 | T_f64

datatype \<comment> \<open>value types\<close>
  t = Nt "nt" | Rt "rt"

datatype \<comment> \<open>packed types\<close>
  tp = Tp_i8 | Tp_i16 | Tp_i32

datatype \<comment> \<open>mutability\<close>
  mut = T_immut | T_mut

record tg = \<comment> \<open>global types\<close>
  tg_sh :: sh
  tg_mut :: mut
  tg_t :: t

datatype \<comment> \<open>function types\<close>
  tf = Tf "sh" "t list" "t list" ("_ _ '_> _" 60)

record tt = \<comment> \<open>table types\<close>
  tt_sh :: sh
  tt_rt :: rt
  tt_n :: "i option"

record mt = \<comment> \<open>memory types\<close>
  mt_sh :: sh
  mt_n :: "i option"

(* TYPING *)
record t_context =
  types_t :: "tf list"
  func_t :: "tf list"
  global :: "tg list"
  table :: "tt"
  memory :: "mt"
  local :: "t list"
  label :: "(t list) list"
  return :: "(t list) option"

record s_context =
  s_inst :: "t_context list"
  s_funcs :: "tf list"
  s_tab  :: "tt list"
  s_mem  :: "mt list"
  s_globs :: "tg list"

datatype
  sx = S | U

datatype
  unop_i = Clz | Ctz | Popcnt

datatype
  unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt

datatype
  unop =
    Unop_i unop_i
    | Unop_f unop_f

datatype
  binop_i = Add | Sub | Mul | Div sx | Rem sx | And | Or | Xor | Shl | Shr sx | Rotl | Rotr

datatype
  binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign

datatype
  binop =
    Binop_i t binop_i
    | Binop_f t binop_f

datatype
  testop = Eqz

datatype
  relop_i = Eq | Ne | Lt sx | Gt sx | Le sx | Ge sx

datatype
  relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef

datatype
  relop =
    Relop_i relop_i
    | Relop_f relop_f

datatype
  cvtop = Convert | Reinterpret

datatype \<comment> \<open>numeric values\<close>
  nv =
    ConstInt32 i32
    | ConstInt64 i64
    | ConstFloat32 f32
    | ConstFloat64 f64

datatype \<comment> \<open>values\<close>
  v =
    NumVal nv
    | NullRef
    | Ref a

record inst = \<comment> \<open>instances\<close>
  types :: "tf list"
  funcs :: "i list"
  tab :: "i option"
  mem :: "i option"
  globs :: "i list"

datatype \<comment> \<open>basic instructions\<close>
  b_e =
    Unreachable
    | Nop
    | Drop
    | Select
    | Block tf "b_e list"
    | Loop tf "b_e list"
    | If tf "b_e list" "b_e list"
    | Br i
    | Br_if i
    | Br_table "i list" i
    | Return
    | Call i
    | Call_indirect ord i
    | Get_local i
    | Set_local i
    | Tee_local i
    | Get_global ord i
    | Set_global ord i
    | Get_table ord
    | Set_table ord
    | Load t ord "(tp \<times> sx) option" a off
    | Store t ord "tp option" a off
    | Rmw t binop "(tp \<times> sx) option" a off
    | Current_memory
    | Current_table
    | Grow_memory
    | Grow_table
    | EConst v ("C _" 60)
    | Unop unop
    | Binop binop
    | Testop t testop
    | Relop relop
    | Cvtop t cvtop t "sx option"
    | Wait t
    | Notify
    | Fork i
    | Instantiate inst

datatype cl = \<comment> \<open>function closures\<close>
  Func_native i tf "t list" "b_e list"
| Func_host tf host

type_synonym tabinst = "(cl option) list"

\<comment> \<open>FIXME: Adding sh is right I think?\<close>
record global =
  g_sh :: sh
  g_mut :: mut
  g_val :: v

record s = \<comment> \<open>store\<close>
  inst :: "inst list"
  funcs :: "cl list"
  tab :: "tabinst list"
  mem :: "mem list"
  globs :: "global list"

datatype fld = Val | Data | Elem | Length

record reg = \<comment> \<open>region\<close>
  Reg_addr :: addr
  Reg_fld :: fld

datatype l = \<comment> \<open>location\<close>
  L_r reg
  | L_ri reg i

datatype e = \<comment> \<open>administrative instruction\<close>
  Basic b_e ("$_" 60)
  | Trap
  | Callcl cl
  | Label nat "e list" "e list"
  | Local nat i "v list" "e list"
  | Ref addr
  | Call_admin addr
  | Fork_admin "e list"
  | Wait_admin l nat
  | Notify_admin l nat inst

datatype Lholed =
    \<comment> \<open>L0 = v* [<hole>] e*\<close>
    LBase "e list" "e list"
    \<comment> \<open>L(i+1) = v* (label n {e* } Li) e*\<close>
  | LRec "e list" nat "e list" Lholed "e list"
end
