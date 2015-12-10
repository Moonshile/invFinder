

open Core.Std
open Utils
open Structure
open Extend

(*
Train Speed Restriction Protocol 

 CONSTANTS 
const num_sections : 15; /* number of rail sections 
const num_tsr : 3; /* number of tsr 
*)

let num_sections = 2

(* TYPES 

type speed_value : enum {
	stop, --clear
	low,
	high,
	full
};*)


let _stop = strc "stop"
let _low = strc "low"
let _high = strc "high"
let _full = strc "full"

let _speed_value = enum "speed_value" [_stop; _low; _high; _full]

(* structure of section 
type section_number : 1..num_sections;*)

let _section_number = enum "section_number" (int_consts (List.map (up_to num_sections) ~f:(fun x -> x + 1)))

(*type section_state : enum {
	idle, -- clear
	busy
};*)

let _idle = strc "idle"
let _busy = strc "busy"

let _section_state = enum "section_state" [_idle; _busy]

(*type section_type :
	record
--		id : section_number;
		status : section_state;
	end;
*)

let _section_type = List.concat [
  [arrdef [("status", [])] "section_state"]
]

(*
 structure of tsr 
type tsr_number : 1..num_tsr;
0表示不存在的TSR 
type TSR_NUMBER : 0..num_tsr;
*)

let _tsr_number = enum "tsr_number" (int_consts [1; 2; 3])
let _TSR_NUMBER = enum "TSR_NUMBER" (int_consts [0; 1; 2; 3])

(*
type tsr_state : enum {
	invalid, -- clear
	valid
};
*)

let _invalid = strc "invalid"
let _valid = strc "valid"

let _tsr_state = enum "tsr_state" [_invalid; _valid]

(*
type tsr_type :
	record
--		id : tsr_number;
		start : section_number;
		close : section_number;
		speed : speed_value;
		status : tsr_state;
	end;		
*)

let _tsr_type = List.concat [
  [arrdef [("start", [])] "section_number"];
  [arrdef [("close", [])] "section_number"];
  [arrdef [("speed", [])] "speed_value"];
  [arrdef [("status", [])] "tsr_state"]
]

(*
type arrtsr_type : array[tsr_number] of tsr_type;

/* movement admission */
type ma_type : 
	record
		start : section_number;
		close : section_number;
	end;

/* structure of train */
type train_type :
	record
		loc : section_number; /* Initial location of train is 1. */
		speed : speed_value;
		ma : ma_type;
		tsr : arrtsr_type;
	end;
*)

let _ma_type = List.concat [
  [arrdef [("start", [])] "section_number"];
  [arrdef [("close", [])] "section_number"];
]

let _train_type = List.concat [
  [arrdef [("loc", [])] "section_number"];
  [arrdef [("speed", [])] "speed_value"];
  record_def "ma" [] _ma_type;
  record_def "tsr" [paramdef "i" "tsr_number"] _tsr_type
]


(*********************************************************************)

let types = [
  _speed_value;
  _section_number;
  _section_state;
  _tsr_number;
  _TSR_NUMBER;
  _tsr_state;
  enum "boolean" [boolc true; boolc false]
]


(*
/* VARIABLES */

var section : array[section_number] of section_type;
var train : train_type;
var tsr : arrtsr_type;
*)

let vardefs = List.concat [
  record_def "section" [paramdef "i0" "section_number"] _section_type;
  record_def "train" [] _train_type;
  record_def "tsr" [paramdef "i" "tsr_number"] _tsr_type
]

let tmp_vardefs = List.concat [
  [arrdef [("mloc", [])] "section_number"];
  [arrdef [("flag", [])] "boolean"];
  [arrdef [("ls", [])] "speed_value"];
  record_def "tmptsr" [paramdef "t" "tsr_number"] _tsr_type;
  record_def "atsr" [] _tsr_type;
  [arrdef [("i", [])] "tsr_number"]
]


let _smt_context =
  Smt.set_context "tsr" (ToSMT.context_of ~types ~vardefs:(vardefs@tmp_vardefs))

(*
/* FUNCTIONS */
*)

(*
/* 计算给定区段的实际限速速度：遍历列车对象的TSR，取其中速度最低者 */
/* @param loc 需要计算实际限速速度的区段号 */
/* @return 实际限速速度 */
function limit_speed(loc: section_number) : speed_value;
var ls : speed_value;
begin
	ls := full; /* full speed of train */
	for t : tsr_number do
		if train.tsr[t].status = valid &  train.tsr[t].start <= loc & loc <= train.tsr[t].close then
			if train.tsr[t].speed = low then 
				ls := low;
			elsif train.tsr[t].speed = high & ls = full then
				ls := high;
			endif;
		endif;
	endfor;
	return ls;
end;
*)

let func_limit_speed loc =
   let ls = global "ls" in
   let statust = record [global "train"; arr [("tsr", [paramref "t"])]; global "status"] in
   let startt = record [global "train"; arr [("tsr", [paramref "t"])]; global "start"] in
   let closet = record [global "train"; arr [("tsr", [paramref "t"])]; global "close"] in
   let speedt = record [global "train"; arr [("tsr", [paramref "t"])]; global "speed"] in
   let s = parallel [
      assign ls (const _full);
      forStatement (
        ifStatement (
          andList [
            eqn (var statust) (const _valid);
            uipPred "<=" [var startt; var (record loc)];
            uipPred "<=" [var (record loc); var closet]
          ]
        ) (
          ifelseStatement (
            eqn (var speedt) (const _low)
          ) (
            assign ls (const _low)
          ) (
            ifStatement (
              andList [eqn (var speedt) (const _high); eqn (var ls) (const _full)]
            ) (
              assign ls (const _high)
            )
          )
        )
      ) [paramdef "t" "tsr_number"]
   ] in
   return ls s ~types
  
                
(* 计算从给定区段起，最长的IDLE状态的区段 */
/* @param loc 给定的区段位置 */
/* @return 最后一个状态为IDLE的区段 */
function max_idle_location(loc: section_number) : section_number;
var mloc : section_number;
var flag : boolean;
begin
	mloc := loc;
  flag := true;
	for s : section_number do
		if s > mloc && flag then 
			if section[s].status = idle then
				mloc := s;
			else
				flag := false;
			endif;
		endif;
	endfor;
	return mloc;
end;*)

let func_max_idle_location loc =
  let mloc = global "mloc" in
  let flag = global "flag" in
  let s = parallel [
    assign mloc (var (record loc));
    assign flag (const (boolc true));
    forStatement (
      ifStatement (
        andList [
          uipPred ">" [param (paramref "s"); var mloc];
          eqn (var flag) (const (boolc true))
        ]
      ) (
        ifelseStatement (
          eqn (var (record [arr [("section", [paramref "s"])]; global "status"])) (const _idle)
        ) (
          assign mloc (param (paramref "s"))
        ) (
          assign flag (const (boolc false))
        )
      )
    ) [paramdef "s" "section_number"]
  ] in
  return mloc s ~types


(* 判断两个TSR是否是同一个TSR，判断依据：起始、结束区段相同并且限速速度也相同 */
/* @param t1 第一个TSR */
/* @param t2 第二个TSR */
/* @return true表示相同，false表示不同 
function equal_tsr(t1,t2: tsr_type) : boolean;
begin
	if t1.start = t2.start & t1.close = t2.close & t1.speed = t2.speed then
		return true;
	else
		return false;
	endif;
end;*)

let fun_equal_tsr t1 t2 =
  let tstart t = var (record (t@[global "start"])) in
  let tclose t = var (record (t@[global "close"])) in
  let tspeed t = var (record (t@[global "speed"])) in
  let cond = andList [
    eqn (tstart t1) (tstart t2);
    eqn (tclose t1) (tclose t2);
    eqn (tspeed t1) (tspeed t2)
  ] in
  ite cond (const (boolc true)) (const (boolc false))

(* 在给定的TSR数组中查找与目标TSR相同的第一个有效（VALID）TSR */
/* @param t 要查找的目标TSR */
/* @param arrt 给定的TSR数组 */
/* @return 查找结果，为索引号，0表示没有找到 
function first_matched_tsr(t: tsr_type; arrt: arrtsr_type): TSR_NUMBER;
begin
	for i : tsr_number do
		if arrt[i].status = valid & equal_tsr(t, arrt[i]) then
			return i;
		endif;
	endfor;
	return 0;	
end;*)

let fun_first_matched_tsr t arrt_i0 =
  let tmp = global "tmp" in
  let s = parallel [
    assign tmp (param (paramfix "i0" "tsr_number" (intc 0)));
    forStatement (
      ifStatement (
        andList [
          eqn (var (record (arrt_i0@[global "status"]))) (const _valid);
          eqn (fun_equal_tsr t arrt_i0) (const (boolc true))
        ]
      ) (
        assign tmp (param (paramref "i0"))
      )
    ) [paramdef "i0" "tsr_number"]
  ] in
  return tmp s ~types


(* 在给定的TSR数组中查找第一个无效（INVALID）TSR */
/* @param arrt 给定的TSR数组 */
/* @return 第一个无效TSR的索引号，0表示没有找到 
function first_invalid_tsr(arrt: arrtsr_type): TSR_NUMBER;
begin
	for i : tsr_number do
		if arrt[i].status = invalid then
			return i;
		endif;
	endfor;
	return 0;	
end;*)

let fun_first_invalid_tsr arrt_i1 =
  let tmp = global "tmp" in
  let s = parallel [
    assign tmp (param (paramfix "i1" "tsr_number" (intc 0)));
    forStatement (
      ifStatement (
        eqn (var (record (arrt_i1@[global "status"]))) (const _invalid)
      ) (
        assign tmp (param (paramref "i1"))
      )
    ) [paramdef "i1" "tsr_number"]
  ] in
  return tmp s ~types


(*
/* 列车临时限速算法的建模，以一个过程表示 */
--rule "RBC computes and issues tsr command"
procedure compute_and_change_tsr();
var 
  /* 临时变量，用于保存搜索到的临时限速内容 */
  tmptsr : arrtsr_type;
  /* 临时变量，用于临时保存计算到的临时限速 */
  atsr : tsr_type;
  /* 临时索引变量 */
  i: tsr_number;
begin
  clear tmptsr;
  -- add init of i
  i := 0;
  /* 以下for和if两行是遍历列车位置区段开始，行车许可范围内的所有区段 */
  for s : section_number do
    if train.loc <= s & s < train.ma.close then
      /* 以下for和if两行是遍历包含当前区段的所有临时限速命令 */
      for t : tsr_number do
        if tsr[t].status = valid & tsr[t].start <= s & s <= tsr[t].close then
          /* 计算到的临时限速暂时保存到atsr中 */
          /* Let atsr record the content of tsr[t] */
          clear atsr;
          atsr.speed := tsr[t].speed;
          /* 起点计算 */
          if tsr[t].start < train.loc then
            /* 若临时限速命令起点区段小于列车位置，则临时限速起点为列车位置 */
            atsr.start := train.loc;
          else
            /* 若临时限速命令起点区段大于等于列车位置，则临时限速起点为命令的起点 */
            atsr.start := tsr[t].start;
          endif;
          /* 终点计算 */
          if tsr[t].close < train.ma.close - 1 then
            /* 若临时限速命令终点区段小于等于行车许可终点区段，则临时限速终点为命令终点 */
            atsr.close := tsr[t].close;
          else
            /* 若临时限速命令终点区段大于行车许可终点，则临时限速终点为行车许可终点 */
            atsr.close := train.ma.close - 1;
          endif;
          /* 如果atsr不在临时变量tmptsr中，则将其加入到tmptsr中 */
          /* Judge whether atsr is in tmptsr, if the answer is yes, put atsr into tmptsr */
          if first_matched_tsr(atsr, tmptsr) = 0 then
            assert first_invalid_tsr(tmptsr) != 0;
            -- move this to head
            -- i := first_invalid_tsr(tmptsr);
            /*
            put "first invalid tsr in tmptsr is ";
            put i;
            put "\n";
            */
            tmptsr[i].status := valid;
            tmptsr[i].start := atsr.start;
            tmptsr[i].close := atsr.close;
            tmptsr[i].speed := atsr.speed;
          endif;
        endif;
      endfor;
      /* 临时限速命令遍历结束 */
    endif;
  endfor;
  /* 区段遍历结束 */
  
  /* 遍历列车的TSR，如果不在上边计算到的临时变量tmptsr中，则将其状态置为INVALID */
  for t : tsr_number do
    if train.tsr[t].status = valid then
      if first_matched_tsr(train.tsr[t], tmptsr) = 0 then
        train.tsr[t].status := invalid;
      endif;
    endif;
  endfor;
  
  /* 遍历计算到的临时变量tmptsr，如果不在列车的TSR中，则将其加入到列车的TSR中 */
  for t : tsr_number do
    if tmptsr[t].status = valid & first_matched_tsr(tmptsr[t], train.tsr) = 0 then
      assert first_invalid_tsr(train.tsr) != 0;
      i := first_invalid_tsr(train.tsr);
      /*
      put "first invalid tsr in train.tsr is ";
      put i;
      put "\n";
      */
      train.tsr[i].status := valid;
      train.tsr[i].start := tmptsr[t].start;
      train.tsr[i].close := tmptsr[t].close;
      train.tsr[i].speed := tmptsr[t].speed;
    endif;
  endfor;
end;
*)

let clear_tsr tsr =
  parallel [
    assign (record (tsr@[global "start"])) (const (intc 1));
    assign (record (tsr@[global "close"])) (const (intc 1));
    assign (record (tsr@[global "speed"])) (const _stop);
    assign (record (tsr@[global "status"])) (const _invalid);
  ]

let proc_compute_and_change_tsr =
  let atsr = global "atsr" in
  let i = global "i" in
  parallel [
    forStatement (clear_tsr [arr [("tmptsr", [paramref "t"])]]) [paramdef "t" "tsr_number"];
    clear_tsr [atsr];
    assign i (param (paramfix "t" "tsr_number" (intc 1)));
    forStatement (
      ifStatement (
        andList [
          uipPred "<=" [var (record [global "train"; global "loc"]); param (paramref "s")];
          uipPred "<" [param (paramref "s"); var (record [global "train"; global "ma"; global "close"])]
        ]
      ) (
        forStatement (
          ifStatement (
            andList [
              eqn (var (record [arr [("tsr", [paramref "t"])]; global "status"])) (const _valid);
              uipPred "<=" [var (record [arr [("tsr", [paramref "t"])]; global "start"]); param (paramref "s")];
              uipPred "<=" [param (paramref "s"); var (record [arr [("tsr", [paramref "t"])]; global "close"])]
            ]
          ) (
            parallel [
              clear_tsr [atsr];
              assign (record [atsr; global "speed"]) (var (record [arr [("tsr", [paramref "t"])]; global "speed"]));
              ifelseStatement (
                uipPred "<" [
                  var (record [arr [("tsr", [paramref "t"])]; global "start"]);
                  var (record [global "train"; global "loc"])
                ]
              ) (
                assign (record [atsr; global "start"]) (var (record [global "train"; global "loc"]))
              ) (
                assign (record [atsr; global "start"]) (var (record [arr [("tsr", [paramref "t"])]; global "start"]))
              );
              ifelseStatement (
                uipPred "<" [
                  var (record [arr [("tsr", [paramref "t"])]; global "close"]);
                  uipFun "-" [
                    var (record [global "train"; global "ma"; global "close"]);
                    const (intc 1)
                  ]
                ]
              ) (
                assign (record [atsr; global "close"]) (var (record [arr [("tsr", [paramref "t"])]; global "close"]))
              ) (
                assign (record [atsr; global "close"]) (uipFun "-" [
                  var (record [global "train"; global "ma"; global "close"]);
                  const (intc 1)
                ])
              );
              ifStatement (
                eqn (fun_first_matched_tsr [atsr] [arr [("tmptsr", [paramref "i0"])]]) (const (intc 0))
              ) (
                parallel [
                  assign i (fun_first_invalid_tsr [arr [("tmptsr", [paramref "i1"])]]);
                  write_param (record [arr [("tmptsr", [paramref "i"])]; global "status"]) [i] (const _valid) ~pds:([paramdef "i" "tsr_number"]);
                  write_param (record [arr [("tmptsr", [paramref "i"])]; global "start"]) [i] (var (record [atsr; global "start"])) ~pds:([paramdef "i" "tsr_number"]);
                  write_param (record [arr [("tmptsr", [paramref "i"])]; global "close"]) [i] (var (record [atsr; global "close"])) ~pds:([paramdef "i" "tsr_number"]);
                  write_param (record [arr [("tmptsr", [paramref "i"])]; global "speed"]) [i] (var (record [atsr; global "speed"])) ~pds:([paramdef "i" "tsr_number"]);
                ]
              )
            ]
          )
        ) [paramdef "t" "tsr_number"]
      )
    ) [paramdef "s" "section_number"];
    
    forStatement (
      ifStatement (
        eqn (var (record [global "train"; arr [("tsr", [paramref "t"])]; global "status"])) (const _valid)
      ) (
        ifStatement (
          eqn (fun_first_matched_tsr [global "train"; arr [("tsr", [paramref "t"])]] [arr [("tmptsr", [paramref "i0"])]]) (const (intc 0))
        ) (
          assign (record [global "train"; arr [("tsr", [paramref "t"])]; global "status"]) (const _invalid)
        )
      )
    ) [paramdef "t" "tsr_number"];

    forStatement (
      ifStatement (
        andList [
          eqn (var (record [arr [("tmptsr", [paramref "t"])]; global "status"])) (const _valid);
          eqn (fun_first_matched_tsr [arr [("tmptsr", [paramref "t"])]] [global "train"; arr [("tsr", [paramref "i0"])]]) (const (intc 0))
        ]
      ) (
        parallel [
          assign i (fun_first_invalid_tsr [global "train"; arr [("tsr", [paramref "i1"])]]);
          write_param (record [global "train"; arr [("tsr", [paramref "i"])]; global "status"]) [i] (const _valid) ~pds:([paramdef "i" "tsr_number"]);
          write_param (record [global "train"; arr [("tsr", [paramref "i"])]; global "start"]) [i] (var (record [arr [("tmptsr", [paramref "t"])]; global "start"])) ~pds:([paramdef "i" "tsr_number"]);
          write_param (record [global "train"; arr [("tsr", [paramref "i"])]; global "close"]) [i] (var (record [arr [("tmptsr", [paramref "t"])]; global "close"])) ~pds:([paramdef "i" "tsr_number"]);
          write_param (record [global "train"; arr [("tsr", [paramref "i"])]; global "speed"]) [i] (var (record [arr [("tmptsr", [paramref "t"])]; global "speed"])) ~pds:([paramdef "i" "tsr_number"]);
        ]
      )
    ) [paramdef "t" "tsr_number"]
  ]


(*
/* 判断在一个TSR数组中是否存在给定的TSR，判断依据：状态为VALID，且起点、终点在范围内，限速速度相同 */
/* @param atsr 给定的TSR */
/* @param arrt TSR数组 */
/* @return true表示存在，false表示不存在 */
function exist_valid_tsr(atsr: tsr_type; arrt: arrtsr_type) : boolean;
begin
  for t : tsr_number do
    if arrt[t].status = valid & arrt[t].speed = atsr.speed &
      arrt[t].start <= atsr.start & atsr.close <= arrt[t].close then
      return true;
    endif;
  endfor;
  return false;
end;
*)

let fun_exist_valid_tsr atsr arrt_i2 =
  ite (
    existFormula [paramdef "i2" "tsr_number"] (
      andList [
        eqn (var (record (arrt_i2@[global "status"]))) (const _valid);
        eqn (var (record (arrt_i2@[global "speed"]))) (var (record (atsr@[global "speed"])));
        uipPred "<=" [var (record (arrt_i2@[global "start"])); var (record (atsr@[global "start"]))];
        uipPred "<=" [var (record (atsr@[global "close"])); var (record (arrt_i2@[global "close"]))]
      ]
    )
  ) (const (boolc true)) (const (boolc false))


(*
/* 判断一个TSR数组中是否存在与给定TSR相对应的TSR，实际上是用来判断能否将列车的TSR中与地面TSR在行车许可中的部分相对应 */
/* @param atsr 给定的（地面）TSR */
/* @param arrt 给定的TSR数组，代表列车上的TSR */
/* @return true表示存在，false表示不存在 */
function exist_correspond_tsr(atsr: tsr_type; arrt: arrtsr_type) : boolean;
var
  bgn, fin: section_number;
begin
  /* 计算给定的地面TSR在列车行车许可范围中的部分 */
  if atsr.start < train.loc then
    bgn := train.loc;
  else
    bgn := atsr.start;
  endif;
  if atsr.close < train.ma.close - 1 then
    fin := atsr.close;
  else
    fin := train.ma.close - 1;
  endif;
  /* 判断是否对应：状态为VALID且起终点和速度都相同 */
  for t : tsr_number do
    if arrt[t].status = valid & arrt[t].speed = atsr.speed &
      arrt[t].start = bgn & arrt[t].close = fin then
      return true;
    endif;
  endfor;
  return false;
end;
*)

let fun_exist_correspond_tsr atsr arrt_i3 =
  let res = global "res" in
  let s = parallel [
    assign (global "bgn") (
      ite (
        uipPred "<" [
          var (record (atsr@[global "start"]));
          var (record [global "train"; global "loc"])
        ]
      ) (
        var (record [global "train"; global "loc"])
      ) (
        var (record (atsr@[global "start"]))
      )
    );
    assign (global "fin") (
      ite (
        uipPred "<" [
          var (record (atsr@[global "close"]));
          uipFun "-" [var (record [global"train"; global "ma"; global "close"]); const (intc 1)]
        ]
      ) (
        var (record (atsr@[global "close"]))
      ) (
        uipFun "-" [var (record [global"train"; global "ma"; global "close"]); const (intc 1)]
      )
    );
    assign res (ite (
      existFormula [paramdef "i3" "tsr_number"] (
        andList [
          eqn (var (record (arrt_i3@[global "status"]))) (const _valid);
          eqn (var (record (arrt_i3@[global "speed"]))) (var (record (atsr@[global "speed"])));
          eqn (var (record (arrt_i3@[global "start"]))) (var (global "bgn"));
          eqn (var (record (arrt_i3@[global "close"]))) (var (global "fin"))
        ]
      )
    ) (const (boolc true)) (const (boolc false)))
  ] in
  return res s ~types


(*
/* 初始状态 */
/* INITIAL STATES */
startstate "Init"
  clear section;
  clear train;
  clear tsr;
  
  /*
  for s : section_number do
    section[s].id := s;
  end;
  
  for t : tsr_number do
    tsr[t].id := t;
    train.tsr[t].id := t;
  end;
  */

  section[1].status := busy;
  train.speed := full;
  train.ma.start := 1;
  train.ma.close := num_sections;
endstartstate;
*)

let clear_section section =
  assign (record (section@[global "status"])) (const _idle)
   
let clearTrain train =
  forStatement (clear_tsr (train@[arr [("tsr", [paramref "t"])]]))  [paramdef "t" "tsr_number"]

let init = parallel[ 
    forStatement (
      clear_section [arr [("section", [paramref "t"])]]
    ) [paramdef "t" "section_number"];
    clearTrain [global "train"];
    forStatement (
      clear_tsr [arr [("tsr", [paramref "t"])]]
    ) [paramdef "t" "tsr_number"];
    assign (record [arr [("section", [paramfix "s" "section_number" (intc 1)])]; global "status"]) (const _busy);
    assign (record [global "train"; global "speed"]) (const _full) ;
    assign (record [global "train"; global "ma"; global "start"]) (const (Intc 1)) ;
    assign (record [global "train"; global "ma"; global "close"]) (const (Intc num_sections))
  ]







(*
/* RULES */

/* 列车运行至下一区段 */
rule "train moves to the next section"
  train.loc < train.ma.close 
==>
begin
  assert train.ma.start <= train.loc &  train.loc < train.ma.close;
  /* 更新区段状态和列车位置 */
  --section[train.loc].status := idle;
  for s : section_number do
    if s = train.loc then
      section[s].status := idle;
    end;
  end;
  train.loc := train.loc + 1;
  --section[train.loc].status := busy;
  for s : section_number do
    if s = train.loc then
      section[s].status := busy;
    end;
  end;
  train.ma.start := train.loc;
  /* 更新临时限速 */
  compute_and_change_tsr();
  
  if train.loc < train.ma.close then
    train.speed := limit_speed(train.loc);
  else
    train.speed := stop;
  endif;  
endrule;
*)

let train_moves_to_the_next_section =
  let name = "train_moves_to_the_next_section" in
  let params = [] in
  let formula = uipPred "<" [
    var (record [global "train"; global "loc"]);
    var (record [global "train"; global "ma"; global "close"])
  ] in
  let statement = parallel [
    forStatement (
      ifStatement (
        eqn (param (paramref "s")) (var (record [global "train"; global "loc"]))
      ) (
        assign (record [arr [("section", [paramref "s"])]; global "status"]) (const _idle)
      )
    ) [paramdef "s" "section_number"];
    assign (record [global "train"; global "loc"]) (
      uipFun "+" [var (record [global "train"; global "loc"]); const (intc 1)]
    );
    forStatement (
      ifStatement (
        eqn (param (paramref "s")) (var (record [global "train"; global "loc"]))
      ) (
        assign (record [arr [("section", [paramref "s"])]; global "status"]) (const _busy)
      )
    ) [paramdef "s" "section_number"];
    assign (record [global "train"; global "ma"; global "start"]) (var (record [global "train"; global "loc"]));
    proc_compute_and_change_tsr;
    assign (record [global "train"; global "speed"]) (
      ite (
        uipPred "<" [
          var (record [global "train"; global "loc"]);
          var (record [global "train"; global "ma"; global "close"])
        ]
      ) (func_limit_speed [global "train"; global "loc"]) (const _stop)
    )
  ] in
  rule name params formula statement





(*
/* 列车更新运行时速度 */
rule "train changes speed"
  train.loc < train.ma.close &  train.speed != limit_speed(train.loc)
==>
begin
  train.speed := limit_speed(train.loc);
endrule;
*)

let train_changes_speed =
  let name = "train_changes_speed" in
  let params = [] in
  let formula = andList [
    uipPred "<" [
      var (record [global "train"; global "loc"]);
      var (record [global "train"; global "ma"; global "close"])
    ];
    neg (eqn (var (record [global "train"; global "speed"])) (func_limit_speed [global "train"; global "loc"]))
  ] in
  let statement =
    assign (record [global "train"; global "speed"]) (func_limit_speed [global "train"; global "loc"])
  in
  rule name params formula statement




(*
ruleset s : section_number do
/* 区段因故障等原因，状态从IDLE变为BUSY */
rule "section state changes from idle to busy"
  section[s].status = idle
  --section[s].status = idle & train.loc < s
==>
begin
  assert s != train.loc;
  section[s].status := busy;
  /* 更新行车许可 */
  if train.ma.start <= s &  s <= train.ma.close then /* the range of ma is decreasing. */
    train.ma.close := s - 1;
  endif;  
  /* 更新临时限速 */
  compute_and_change_tsr();
endrule;
endruleset;
*)

let section_state_changes_from_idle_to_busy =
  let name = "section_state_changes_from_idle_to_busy" in
  let params = [paramdef "sec" "section_number"] in
  let formula = eqn (
    var (record [arr [("section", [paramref "sec"])]; global "status"])
  ) (const _idle) in
  let statement = parallel [
    assign (record [arr [("section", [paramref "sec"])]; global "status"]) (const _busy);
    ifStatement (
      andList [
        uipPred "<=" [var (record [global "train"; global "ma"; global "start"]); param (paramref "sec")];
        uipPred "<=" [param (paramref "sec"); var (record [global "train"; global "ma"; global "close"])]
      ]
    ) (
      assign (record [global "train"; global "ma"; global "close"]) (uipFun "-" [param (paramref "sec"); const (intc 1)])
    );
    proc_compute_and_change_tsr;
  ] in
  rule name params formula statement







(*
ruleset s : section_number do
/* 区段因故障排除等原因，状态从BUSY变为IDLE */
rule "section state changes from busy to idle"
  section[s].status = busy & train.loc != s
  --section[s].status = busy & train.loc < s
==>
begin
  section[s].status := idle;
  /* 更新行车许可 */
  train.ma.close := max_idle_location(train.ma.close); /* the range of ma is enlarging. */
  /* 更新临时限速 */
  compute_and_change_tsr();
endrule;
endruleset;
*)

let section_state_changes_from_busy_to_idle =
  let name = "section_state_changes_from_busy_to_idle" in
  let params = [paramdef "sec" "section_number"] in
  let formula = andList [
    eqn (var (record [arr [("section", [paramref "sec"])]; global "status"])) (const _busy);
    neg (eqn (var (record [global "train"; global "loc"])) (param (paramref "sec")))
  ] in
  let statement = parallel [
    assign (record [arr [("section", [paramref "sec"])]; global "status"]) (const _idle);
    assign (record [global "train"; global "ma"; global "close"]) (func_max_idle_location [global "train"; global "ma"; global "close"]);
    proc_compute_and_change_tsr;
  ] in
  rule name params formula statement





(*
ruleset t : tsr_number; bgn : section_number; fin : section_number; spd : speed_value do
/* 地面出现新的临时限速命令 */
/* 为保证最多3个临时限速，当已经存在3个临时限速命令时，就暂时不再出现新的 */
rule "tsr condition is enabled"
  tsr[t].status = invalid &  bgn < fin &  spd != stop &  spd != full
==>
begin
  tsr[t].status := valid;
  tsr[t].start := bgn;
  tsr[t].close := fin;
  tsr[t].speed := spd;
  /* 更新临时限速 */
  compute_and_change_tsr();
endrule;
endruleset;
*)

let tsr_condition_is_enabled =
  let name = "tsr_condition_is_enabled" in
  let params = [
    paramdef "tnum" "tsr_number";
    paramdef "bgn" "section_number";
    paramdef "fin" "section_number";
    paramdef "spd" "speed_value"
  ] in
  let formula = andList [
    eqn (var (record [arr [("tsr", [paramref "tnum"])]; global "status"])) (const _invalid);
    uipPred "<" [param (paramref "bgn"); param (paramref "fin")];
    neg (eqn (param (paramref "spd")) (const _stop));
    neg (eqn (param (paramref "spd")) (const _full))
  ] in
  let statement = parallel [
    assign (record [arr [("tsr", [paramref "tnum"])]; global "status"]) (const _valid);
    assign (record [arr [("tsr", [paramref "tnum"])]; global "start"]) (param (paramref "bgn"));
    assign (record [arr [("tsr", [paramref "tnum"])]; global "close"]) (param (paramref "fin"));
    assign (record [arr [("tsr", [paramref "tnum"])]; global "speed"]) (param (paramref "spd"));
    proc_compute_and_change_tsr;
  ] in
  rule name params formula statement






(*
ruleset t : tsr_number do
/* 地面取消临时限速命令 */
rule "tsr condition is disabled"
  tsr[t].status = valid
==>
begin
  clear tsr[t];
  /* 更新临时限速 */
  compute_and_change_tsr();
endrule;
endruleset;
*)

let tsr_condition_is_disabled =
  let name = "tsr_condition_is_disabled" in
  let params = [paramdef "tnum" "tsr_number"] in
  let formula = eqn (var (record [arr [("tsr", [paramref "tnum"])]; global "status"])) (const _valid) in
  let statement = parallel [
    clear_tsr [arr [("tsr", [paramref "tnum"])]];
    proc_compute_and_change_tsr;
  ] in
  rule name params formula statement





let rules = [
  train_moves_to_the_next_section;
  (*train_changes_speed;
  section_state_changes_from_idle_to_busy;
  section_state_changes_from_busy_to_idle;
  tsr_condition_is_enabled;
  tsr_condition_is_disabled*)
]






(*

/* Invariants */

/* 地面TSR在行车许可范围内的部分一定也在列车TSR中。 换句话说，
如果tsr[t]是一个应发出的限速命令，那么它一定被发到train.tsr */
ruleset t : tsr_number do
  invariant "valid tsr is always sent to train's tsr"
  (tsr[t].status = valid & train.loc < tsr[t].close & tsr[t].start < train.ma.close - 1) -> 
  (exist_correspond_tsr(tsr[t], train.tsr) = true)
end;
*)

let valid_tsr_is_always_sent_to_trains_tsr =
  let name = "valid_tsr_is_always_sent_to_trains_tsr" in
  let params = [paramdef "tnum" "tsr_number"] in
  let formula =
    imply (
      andList [
        eqn (var (record [arr [("tsr", [paramref "tnum"])]; global "status"])) (const _valid);
        uipPred "<" [
          var (record [global "train"; global "loc"]);
          var (record [arr [("tsr", [paramref "tnum"])]; global "close"])
        ];
        uipPred "<" [
          var (record [arr [("tsr", [paramref "tnum"])]; global "start"]);
          uipFun "-" [var (record [global "train"; global "ma"; global "close"]); const (intc 1)]
        ]
      ]
    ) (
      eqn (fun_exist_correspond_tsr [arr [("tsr", [paramref "tnum"])]] [global "train"; arr [("tsr", [paramref "i3"])]]) (const (boolc true))
    )
  in
  prop name params formula






(*
/* 列车上的TSR一定能在地面TSR中找到。与此等价的性质是：
如果非法限速命令不及时撤销，Murphi将会在某一状态至少发现一个错误的tsr。*/
ruleset t : tsr_number do
  invariant "train's tsr is always legal"
  (train.tsr[t].status = valid) -> (exist_valid_tsr(train.tsr[t], tsr) = true)
end;
*)

let trains_tsr_is_always_legal =
  let name = "trains_tsr_is_always_legal" in
  let params = [paramdef "tnum" "tsr_number"] in
  let formula =
    imply (
      eqn (var (record [global "train"; arr [("tsr", [paramref "tnum"])]; global "status"])) (const _valid)
    ) (
      eqn (fun_exist_valid_tsr [global "train"; arr [("tsr", [paramref "tnum"])]] [arr [("tsr", [paramref "i2"])]]) (const (boolc true))
    )
  in
  prop name params formula





(*
ruleset t : tsr_number do
  invariant "valid train's tsr is complied with train's location" 
  (train.tsr[t].status = valid) -> (train.loc <= train.tsr[t].start & 
  train.tsr[t].close < train.ma.close)
end;
*)

let valid_trains_tsr_is_complied_with_trains_location =
  let name = "valid_trains_tsr_is_complied_with_trains_location" in
  let params = [paramdef "tnum" "tsr_number"] in
  let formula =
    imply (
      eqn (var (record [global "train"; arr [("tsr", [paramref "tnum"])]; global "status"])) (const _valid)
    ) (
      andList [
        uipPred "<=" [
          var (record [global "train"; global "loc"]);
          var (record [global "train"; arr [("tsr", [paramref "tnum"])]; global "start"])
        ];
        uipPred "<" [
          var (record [global "train"; arr [("tsr", [paramref "tnum"])]; global "close"]);
          var (record [global "train"; global "ma"; global "close"])
        ]
      ]
    )
  in
  prop name params formula




let properties = [
  valid_tsr_is_always_sent_to_trains_tsr;
  trains_tsr_is_always_legal;
  valid_trains_tsr_is_complied_with_trains_location
]



let protocol = {
  name = "tsr";
  types;
  vardefs;
  init;
  rules;
  properties;
}



let down_str = ToSMV.protocol_act (Preprocess.protocol_act protocol) in
Out_channel.write_all "tsr.smv" ~data:down_str;;


