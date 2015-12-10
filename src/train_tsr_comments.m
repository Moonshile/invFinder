/* Train Speed Restriction Protocol */

/* CONSTANTS */
const num_sections : 15; /* number of rail sections */
const num_tsr : 3; /* number of tsr */

/* TYPES */

type speed_value : enum {
	stop, --clear
	low,
	high,
	full
};


/* structure of section */
type section_number : 1..num_sections;

type section_state : enum {
	idle, -- clear
	busy
};

type section_type :
	record
--		id : section_number;
		status : section_state;
	end;

/* structure of tsr */
type tsr_number : 1..num_tsr;
/* 0表示不存在的TSR */
type TSR_NUMBER : 0..num_tsr;


type tsr_state : enum {
	invalid, -- clear
	valid
};

type tsr_type :
	record
--		id : tsr_number;
		start : section_number;
		close : section_number;
		speed : speed_value;
		status : tsr_state;
	end;		

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


/* VARIABLES */

var section : array[section_number] of section_type;
var train : train_type;
var tsr : arrtsr_type;

/* FUNCTIONS */

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

/* 计算从给定区段起，最长的IDLE状态的区段 */
/* @param loc 给定的区段位置 */
/* @return 最后一个状态为IDLE的区段 */
function max_idle_location(loc: section_number) : section_number;
var mloc : section_number;
begin
	mloc := loc;
	for s : section_number do
		if s > mloc then 
			if section[s].status = idle then
				mloc := s;
			else
				return mloc;
			endif;
		endif;
	endfor;
	return mloc;
end;

/* 判断两个TSR是否是同一个TSR，判断依据：起始、结束区段相同并且限速速度也相同 */
/* @param t1 第一个TSR */
/* @param t2 第二个TSR */
/* @return true表示相同，false表示不同 */
function equal_tsr(t1,t2: tsr_type) : boolean;
begin
	if t1.start = t2.start & t1.close = t2.close & t1.speed = t2.speed then
		return true;
	else
		return false;
	endif;
end;

/* 在给定的TSR数组中查找与目标TSR相同的第一个有效（VALID）TSR */
/* @param t 要查找的目标TSR */
/* @param arrt 给定的TSR数组 */
/* @return 查找结果，为索引号，0表示没有找到 */
function first_matched_tsr(t: tsr_type; arrt: arrtsr_type): TSR_NUMBER;
begin
	for i : tsr_number do
		if arrt[i].status = valid & equal_tsr(t, arrt[i]) then
			return i;
		endif;
	endfor;
	return 0;	
end;

/* 在给定的TSR数组中查找第一个无效（INVALID）TSR */
/* @param arrt 给定的TSR数组 */
/* @return 第一个无效TSR的索引号，0表示没有找到 */
function first_invalid_tsr(arrt: arrtsr_type): TSR_NUMBER;
begin
	for i : tsr_number do
		if arrt[i].status = invalid then
			return i;
		endif;
	endfor;
	return 0;	
end;

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
						i := first_invalid_tsr(tmptsr);
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


/* RULES */

/* 列车运行至下一区段 */
rule "train moves to the next section"
	train.loc < train.ma.close 
==>
begin
	assert train.ma.start <= train.loc &  train.loc < train.ma.close;
	/* 更新区段状态和列车位置 */
	section[train.loc].status := idle;
	train.loc := train.loc + 1;
	section[train.loc].status := busy;
	train.ma.start := train.loc;
	/* 更新临时限速 */
	compute_and_change_tsr();
	
	if train.loc < train.ma.close then
		train.speed := limit_speed(train.loc);
	else
		train.speed := stop;
	endif;	
endrule;

/* 列车更新运行时速度 */
rule "train changes speed"
	train.loc < train.ma.close &  train.speed != limit_speed(train.loc)
==>
begin
	train.speed := limit_speed(train.loc);
endrule;


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

/* Invariants */

/* 地面TSR在行车许可范围内的部分一定也在列车TSR中。 换句话说，
如果tsr[t]是一个应发出的限速命令，那么它一定被发到train.tsr */
ruleset t : tsr_number do
	invariant "valid tsr is always sent to train's tsr"
	(tsr[t].status = valid & train.loc < tsr[t].close & tsr[t].start < train.ma.close - 1) -> 
	(exist_correspond_tsr(tsr[t], train.tsr) = true)
end;

/* 列车上的TSR一定能在地面TSR中找到。与此等价的性质是：
如果非法限速命令不及时撤销，Murphi将会在某一状态至少发现一个错误的tsr。*/
ruleset t : tsr_number do
	invariant "train's tsr is always legal"
	(train.tsr[t].status = valid) -> (exist_valid_tsr(train.tsr[t], tsr) = true)
end;

/*
ruleset t : tsr_number do
	invariant "valid train's tsr is complied with train's location" 
	(train.tsr[t].status = valid) -> (train.loc <= train.tsr[t].start & 
	train.tsr[t].close < train.ma.close)
end;
*/
