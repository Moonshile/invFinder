

open Core.Std
open Utils
open Structure
open Extend

let name = "tsr_test_proc_as_rule"

let num_sections = 15
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
  record_def "tsr" [paramdef "i1" "tsr_number"] _tsr_type;
  [arrdef [("x", [])] "boolean"];
  record_def "tmptsr" [paramdef "i2" "tsr_number"] _tsr_type;
  record_def "atsr" [] _tsr_type
]

let tmp_vardefs = List.concat [
  [arrdef [("mloc", [])] "section_number"];
  [arrdef [("flag", [])] "boolean"];
  [arrdef [("ls", [])] "speed_value"];
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





let compute_and_change_tsr =
  let name = "compute_and_change_tsr" in
  let params = [
    paramdef "s" "section_number";
  ] in
  let formula = eqn (var (global "x")) (const (boolc true)) in
  let i = global "i" in
  let atsr = global "atsr" in
  let statement = parallel [
    ifStatement (eqn (param (paramref "s")) (const (intc 1))) (
      parallel [
        forStatement (clear_tsr [arr [("tmptsr", [paramref "t"])]]) [paramdef "t" "tsr_number"];
        clear_tsr [atsr];
      ]
    );

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
                var (record [global "train"; global "ma"; global "close"])
              ]
            ) (
              assign (record [atsr; global "close"]) (var (record [arr [("tsr", [paramref "t"])]; global "close"]))
            ) (
              assign (record [atsr; global "close"]) (
                var (record [global "train"; global "ma"; global "close"])
              )
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
    );
    ifStatement (eqn (param (paramref "s")) (const (intc num_sections))) (parallel [
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
    ]);
    
    assign (global "x") (const (boolc false))
  ] in
  rule name params formula statement






let rules = [
  compute_and_change_tsr;
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

