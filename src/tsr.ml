

open Core.Std
open Utils
open Structure
open Extend

let name = "tsr"

let num_sections = 3
let num_tsr = 3


let _stop = strc "stop"
let _low = strc "low"
let _high = strc "high"
let _full = strc "full"

let _speed_value = enum "speed_value" [_stop; _low; _high; _full]

let _section_number = enum "section_number" (int_consts (List.map (up_to num_sections) ~f:(fun x -> x + 1)))

let _idle = strc "idle"
let _busy = strc "busy"

let _section_state = enum "section_state" [_idle; _busy]

let _section_type = List.concat [
  [arrdef [("status", [])] "section_state"]
]

let _tsr_number = enum "tsr_number" (int_consts (List.map (up_to num_tsr) ~f:(fun x -> x + 1)))
let _TSR_NUMBER = enum "TSR_NUMBER" (int_consts (up_to (num_tsr + 1)))

let _invalid = strc "invalid"
let _valid = strc "valid"

let _tsr_state = enum "tsr_state" [_invalid; _valid]

let _tsr_type = List.concat [
  [arrdef [("start", [])] "section_number"];
  [arrdef [("close", [])] "section_number"];
  [arrdef [("speed", [])] "speed_value"];
  [arrdef [("status", [])] "tsr_state"]
]

let _ma_type = List.concat [
  [arrdef [("start", [])] "section_number"];
  [arrdef [("close", [])] "section_number"];
  [arrdef [("stopend", [])] "boolean"]
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
  [arrdef [("i", [])] "tsr_number"];
  [arrdef [("tmp", [])] "tsr_number"]
]


let _smt_context =
  Smt.set_context name (ToSMT.context_of ~types ~vardefs:(vardefs@tmp_vardefs))

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
            uipPred "<=" [var startt; loc];
            uipPred "<=" [loc; var closet]
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

let func_max_idle_location idled loc =
  let mloc = global "mloc" in
  let flag = global "flag" in
  let s = parallel [
    assign mloc loc;
    assign flag (const (boolc true));
    forStatement (
      ifStatement (
        andList [
          uipPred ">" [param (paramref "s"); var mloc];
          eqn (var flag) (const (boolc true))
        ]
      ) (
        ifelseStatement (
          orList [
            eqn (var (record [arr [("section", [paramref "s"])]; global "status"])) (const _idle);
            eqn (param (paramref "s")) idled
          ]
        ) (
          assign mloc (param (paramref "s"))
        ) (
          assign flag (const (boolc false))
        )
      )
    ) [paramdef "s" "section_number"]
  ] in
  return mloc s ~types

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

let fun_first_matched_tsr t arrt_i0 =
  let tmp = global "tmp" in
  let flag = global "flag" in
  let s = parallel [
    assign tmp (param (paramfix "i0" "tsr_number" (intc 0)));
    assign flag (const (boolc true));
    forStatement (
      ifStatement (
        andList [
          eqn (var (record (arrt_i0@[global "status"]))) (const _valid);
          eqn (fun_equal_tsr t arrt_i0) (const (boolc true));
          eqn (var flag) (const (boolc true))
        ]
      ) (
        parallel [
          assign tmp (param (paramref "i0"));
          assign flag (const (boolc false))
        ]
      )
    ) [paramdef "i0" "tsr_number"]
  ] in
  return tmp s ~types

let fun_first_invalid_tsr arrt_i1 =
  let tmp = global "tmp" in
  let flag = global "flag" in
  let s = parallel [
    assign tmp (param (paramfix "i1" "tsr_number" (intc 0)));
    assign flag (const (boolc true));
    forStatement (
      ifStatement (
        andList [
          eqn (var (record (arrt_i1@[global "status"]))) (const _invalid);
          eqn (var flag) (const (boolc true))
        ]
      ) (
        parallel [
          assign tmp (param (paramref "i1"));
          assign flag (const (boolc false))
        ]
      )
    ) [paramdef "i1" "tsr_number"]
  ] in
  return tmp s ~types

let clear_tsr tsr =
  parallel [
    assign (record (tsr@[global "start"])) (const (intc 1));
    assign (record (tsr@[global "close"])) (const (intc 1));
    assign (record (tsr@[global "speed"])) (const _stop);
    assign (record (tsr@[global "status"])) (const _invalid);
  ]

let proc_compute_and_change_tsr train_loc train_ma_close =
  let atsr = global "atsr" in
  let i = global "i" in
  parallel [
    forStatement (clear_tsr [arr [("tmptsr", [paramref "t"])]]) [paramdef "t" "tsr_number"];
    clear_tsr [atsr];
    assign i (param (paramfix "t" "tsr_number" (intc 1)));
    forStatement (
      ifStatement (
        andList [
          uipPred "<=" [train_loc; param (paramref "s")];
          uipPred "<" [param (paramref "s"); train_ma_close]
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
                  train_loc
                ]
              ) (
                assign (record [atsr; global "start"]) (train_loc)
              ) (
                assign (record [atsr; global "start"]) (var (record [arr [("tsr", [paramref "t"])]; global "start"]))
              );
              ifelseStatement (
                uipPred "<" [
                  var (record [arr [("tsr", [paramref "t"])]; global "close"]);
                  train_ma_close;
                ]
              ) (
                assign (record [atsr; global "close"]) (var (record [arr [("tsr", [paramref "t"])]; global "close"]))
              ) (
                assign (record [atsr; global "close"]) train_ma_close
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
          var (record [global"train"; global "ma"; global "close"])
        ]
      ) (
        var (record (atsr@[global "close"]))
      ) (
        var (record [global"train"; global "ma"; global "close"])
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
    assign (record [global "train"; global "ma"; global "close"]) (const (Intc num_sections));
    assign (record [global "train"; global "ma"; global "stopend"]) (const (boolc false))
  ]







let train_moves_to_the_next_section =
  let name = "train_moves_to_the_next_section" in
  let params = [
    paramdef "train_loc" "section_number";
    paramdef "train_ma_close" "section_number"
  ] in
  let train_loc = paramref "train_loc" in
  let train_ma_close = paramref "train_ma_close" in
  let train_loc_plus_1 = uipFun "+" [param train_loc; const (intc 1)] in
  let formula = andList [
    eqn (var (record [global "train"; global "loc"])) (param train_loc);
    eqn (var (record [global "train"; global "ma"; global "close"])) (param train_ma_close);
    uipPred "<" [param train_loc; param train_ma_close]
  ] in
  let statement = parallel [
    assign (record [arr [("section", [train_loc])]; global "status"]) (const _idle);
    assign (record [global "train"; global "loc"]) train_loc_plus_1;
    forStatement (
      ifStatement (
        eqn (param (paramref "s")) train_loc_plus_1
      ) (
        assign (record [arr [("section", [paramref "s"])]; global "status"]) (const _busy)
      )
    ) [paramdef "s" "section_number"];
    assign (record [global "train"; global "ma"; global "start"]) train_loc_plus_1;
    proc_compute_and_change_tsr train_loc_plus_1 (param train_ma_close);
    assign (record [global "train"; global "speed"]) (
      let g = orList [
        uipPred "<" [train_loc_plus_1; param train_ma_close];
        eqn (var (record [global "train"; global "ma"; global "stopend"])) (const (boolc false))
      ] in
      ite g (func_limit_speed train_loc_plus_1) (const _stop)
    )
  ] in
  rule name params formula statement





let train_changes_speed =
  let name = "train_changes_speed" in
  let params = [
    paramdef "train_loc" "section_number";
    paramdef "train_ma_close" "section_number"
  ] in
  let train_loc = paramref "train_loc" in
  let train_ma_close = paramref "train_ma_close" in
  let formula = andList [
    eqn (var (record [global "train"; global "loc"])) (param train_loc);
    eqn (var (record [global "train"; global "ma"; global "close"])) (param train_ma_close);
    uipPred "<=" [param train_loc; param train_ma_close];
    neg (eqn (var (record [global "train"; global "speed"])) (func_limit_speed (param train_loc)))
  ] in
  let statement =
    let value = ite (
      orList [
        uipPred "<" [param train_loc; param train_ma_close];
        eqn (var (record [global "train"; global "ma"; global "stopend"])) (const (boolc false))
      ]
    ) (
      func_limit_speed (param train_loc)
    ) (
      const _stop
    ) in
    assign (record [global "train"; global "speed"]) value
  in
  rule name params formula statement






let whether_train_reaches_its_stopend =
  let name = "whether_train_reaches_its_stopend" in
  let params = [] in
  let formula = andList [
    eqn (var (record [global "train"; global "loc"])) (var (record [global "train"; global "ma"; global "close"]));
    eqn (var (record [global "train"; global "ma"; global "stopend"])) (const (boolc false))
  ] in
  let statement = assign (record [global "train"; global "ma"; global "stopend"]) (const (boolc true)) in
  rule name params formula statement









let section_state_changes_from_idle_to_busy =
  let name = "section_state_changes_from_idle_to_busy" in
  let params = [
    paramdef "sec" "section_number";
    paramdef "train_loc" "section_number";
    paramdef "train_ma_close" "section_number";
    paramdef "train_ma_start" "section_number";
  ] in
  let train_loc = paramref "train_loc" in
  let train_ma_close = paramref "train_ma_close" in
  let train_ma_start = paramref "train_ma_start" in
  let sec_minus_1 = uipFun "-" [param (paramref "sec"); const (intc 1)] in
  let formula = andList [
    eqn (var (record [global "train"; global "loc"])) (param train_loc);
    eqn (var (record [global "train"; global "ma"; global "close"])) (param train_ma_close);
    eqn (var (record [global "train"; global "ma"; global "start"])) (param train_ma_start);
    eqn (var (record [arr [("section", [paramref "sec"])]; global "status"])) (const _idle);
    uipPred "<" [param train_loc; param (paramref "sec")]
  ] in
  let if_cond = andList [
    uipPred "<=" [param train_ma_start; param (paramref "sec")];
    uipPred "<=" [param (paramref "sec"); param train_ma_close]
  ] in
  let statement = parallel [
    assign (record [arr [("section", [paramref "sec"])]; global "status"]) (const _busy);
    ifStatement if_cond (parallel [
      assign (record [global "train"; global "ma"; global "close"]) sec_minus_1;
      assign (record [global "train"; global "ma"; global "stopend"]) (const (boolc false))
    ]);
    proc_compute_and_change_tsr (param train_loc) (ite if_cond sec_minus_1 (param train_ma_close));
  ] in
  rule name params formula statement








let section_state_changes_from_busy_to_idle =
  let name = "section_state_changes_from_busy_to_idle" in
  let params = [
    paramdef "sec" "section_number";
    paramdef "train_loc" "section_number";
    paramdef "train_ma_close" "section_number";
    paramdef "new_close" "section_number";
  ] in
  let train_loc = paramref "train_loc" in
  let train_ma_close = paramref "train_ma_close" in
  let new_close = paramref "new_close" in
  let formula = andList [
    eqn (var (record [global "train"; global "loc"])) (param train_loc);
    eqn (var (record [global "train"; global "ma"; global "close"])) (param train_ma_close);
    eqn (param new_close) (func_max_idle_location (param (paramref "sec")) (param train_ma_close));
    eqn (var (record [arr [("section", [paramref "sec"])]; global "status"])) (const _busy);
    uipPred "<" [param train_loc; param (paramref "sec")]
  ] in
  let statement = parallel [
    assign (record [arr [("section", [paramref "sec"])]; global "status"]) (const _idle);
    assign (record [global "train"; global "ma"; global "close"]) (param new_close);
    ifStatement (neg (eqn (param new_close) (param (paramref "sec")))) (
      assign (record [global "train"; global "ma"; global "stopend"]) (const (boolc false))
    );
    proc_compute_and_change_tsr (param train_loc) (param new_close);
  ] in
  rule name params formula statement





let tsr_condition_is_enabled =
  let name = "tsr_condition_is_enabled" in
  let params = [
    paramdef "tnum" "tsr_number";
    paramdef "bgn" "section_number";
    paramdef "fin" "section_number";
    paramdef "spd" "speed_value";
    paramdef "train_loc" "section_number";
    paramdef "train_ma_close" "section_number";
  ] in
  let train_loc = paramref "train_loc" in
  let train_ma_close = paramref "train_ma_close" in
  let formula = andList [
    eqn (var (record [global "train"; global "loc"])) (param train_loc);
    eqn (var (record [global "train"; global "ma"; global "close"])) (param train_ma_close);
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
    proc_compute_and_change_tsr (param train_loc) (param train_ma_close);
  ] in
  rule name params formula statement








let tsr_condition_is_disabled =
  let name = "tsr_condition_is_disabled" in
  let params = [
    paramdef "tnum" "tsr_number";
    paramdef "train_loc" "section_number";
    paramdef "train_ma_close" "section_number";
  ] in
  let train_loc = paramref "train_loc" in
  let train_ma_close = paramref "train_ma_close" in
  let formula = andList [
    eqn (var (record [global "train"; global "loc"])) (param train_loc);
    eqn (var (record [global "train"; global "ma"; global "close"])) (param train_ma_close);
    eqn (var (record [arr [("tsr", [paramref "tnum"])]; global "status"])) (const _valid)
  ] in
  let statement = parallel [
    clear_tsr [arr [("tsr", [paramref "tnum"])]];
    proc_compute_and_change_tsr (param train_loc) (param train_ma_close);
  ] in
  rule name params formula statement





let rules = [
  train_moves_to_the_next_section;
  train_changes_speed;
  whether_train_reaches_its_stopend;
  section_state_changes_from_idle_to_busy;
  section_state_changes_from_busy_to_idle;
  tsr_condition_is_enabled;
  tsr_condition_is_disabled
]







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
          var (record [global "train"; global "ma"; global "close"])
        ]
      ]
    ) (
      eqn (fun_exist_correspond_tsr [arr [("tsr", [paramref "tnum"])]] [global "train"; arr [("tsr", [paramref "i3"])]]) (const (boolc true))
    )
  in
  prop name params formula







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
        uipPred "<=" [
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
  name;
  types;
  vardefs;
  init;
  rules;
  properties;
}



let down_str = ToSMV.protocol_act (Preprocess.protocol_act protocol) in
Out_channel.write_all (sprintf "%s.smv" name) ~data:down_str;;


