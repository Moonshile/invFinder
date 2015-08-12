
const

  NODE_NUM : 5;

type

  NODE : 0..NODE_NUM;

  CACHE_STATE : enum {CACHE_I, CACHE_S, CACHE_E};

  NODE_CMD : enum {NODE_None, NODE_Get, NODE_GetX};

  NODE_STATE : record
    ProcCmd : NODE_CMD;
    InvMarked : boolean;
    CacheState : CACHE_STATE;
  end;

  DIR_STATE : record
    Pending : boolean;
    Local : boolean;
    Dirty : boolean;
    HeadVld : boolean;
    HeadPtr : NODE;
    ShrVld : boolean;
    ShrSet : array [NODE] of boolean;
    InvSet : array [NODE] of boolean;
  end;

  UNI_CMD : enum {UNI_None, UNI_Get, UNI_GetX, UNI_Put, UNI_PutX, UNI_Nak};

  UNI_MSG : record
    Cmd : UNI_CMD;
    Proc : NODE;
  end;

  INV_CMD : enum {INV_None, INV_Inv, INV_InvAck};

  INV_MSG : record
    Cmd : INV_CMD;
  end;

  RP_CMD : enum {RP_None, RP_Replace};

  RP_MSG : record
    Cmd : RP_CMD;
  end;

  WB_CMD : enum {WB_None, WB_Wb};

  WB_MSG : record
    Cmd : WB_CMD;
    Proc : NODE;
  end;

  SHWB_CMD : enum {SHWB_None, SHWB_ShWb, SHWB_FAck};

  SHWB_MSG : record
    Cmd : SHWB_CMD;
    Proc : NODE;
  end;

  NAKC_CMD : enum {NAKC_None, NAKC_Nakc};

  NAKC_MSG : record
    Cmd : NAKC_CMD;
  end;

  STATE : record
    Proc : array [NODE] of NODE_STATE;
    Dir : DIR_STATE;
    UniMsg : array [NODE] of UNI_MSG;
    InvMsg : array [NODE] of INV_MSG;
    RpMsg : array [NODE] of RP_MSG;
    WbMsg : WB_MSG;
    ShWbMsg : SHWB_MSG;
    NakcMsg : NAKC_MSG;
  end;

var

  Home : NODE;
  Sta : STATE;


ruleset h : NODE do
startstate "Init"
  Home := h;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.Dir.HeadPtr := h;
  Sta.Dir.ShrVld := false;
  Sta.WbMsg.Cmd := WB_None;
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.NakcMsg.Cmd := NAKC_None;
  for p : NODE do
    Sta.Proc[p].ProcCmd := NODE_None;
    Sta.Proc[p].InvMarked := false;
    Sta.Proc[p].CacheState := CACHE_I;
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
    Sta.UniMsg[p].Cmd := UNI_None;
    Sta.InvMsg[p].Cmd := INV_None;
    Sta.RpMsg[p].Cmd := RP_None;
  end;
endstartstate;
endruleset;

rule "PI_Local_GetX_PutX"
  Sta.Proc[Home].ProcCmd = NODE_None &
  ( Sta.Proc[Home].CacheState = CACHE_I |
    Sta.Proc[Home].CacheState = CACHE_S ) &
  !Sta.Dir.Pending & !Sta.Dir.Dirty
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  if (Sta.Dir.HeadVld) then
    Sta.Dir.Pending := true;
    Sta.Dir.HeadVld := false;
    Sta.Dir.ShrVld := false;
    for p : NODE do
      Sta.Dir.ShrSet[p] := false;
      if ( p != Home &
           ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
             Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p ) ) then
        Sta.Dir.InvSet[p] := true;
        Sta.InvMsg[p].Cmd := INV_Inv;
      else
        Sta.Dir.InvSet[p] := false;
        Sta.InvMsg[p].Cmd := INV_None;
      end;
    end;
  end;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
endrule;

invariant "CacheStateProp"
  !(Sta.Dir.InvSet[3] & Sta.UniMsg[1].Cmd = UNI_Get & Sta.UniMsg[1].Proc = 2);

















