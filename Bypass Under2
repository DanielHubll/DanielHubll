local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 16) then
					if (Enum <= 7) then
						if (Enum <= 3) then
							if (Enum <= 1) then
								if (Enum > 0) then
									Stk[Inst[2]] = Inst[3];
								else
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum > 2) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 5) then
							if (Enum == 4) then
								do
									return;
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum == 6) then
							Stk[Inst[2]] = {};
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 19) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 11) then
						if (Enum <= 9) then
							if (Enum == 8) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 10) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 19) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 13) then
						if (Enum > 12) then
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 14) then
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 15) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					else
						do
							return;
						end
					end
				elseif (Enum <= 25) then
					if (Enum <= 20) then
						if (Enum <= 18) then
							if (Enum == 17) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum > 19) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 22) then
						if (Enum == 21) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 23) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					elseif (Enum > 24) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					else
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					end
				elseif (Enum <= 29) then
					if (Enum <= 27) then
						if (Enum > 26) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						end
					elseif (Enum == 28) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 31) then
					if (Enum == 30) then
						Stk[Inst[2]][Inst[3]] = Inst[4];
					else
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					end
				elseif (Enum <= 32) then
					Stk[Inst[2]][Inst[3]] = Inst[4];
				elseif (Enum == 33) then
					VIP = Inst[3];
				else
					local A = Inst[2];
					Stk[A](Stk[A + 1]);
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!143Q0003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C61796572030A3Q004765745365727669636503053Q005465616D7303043Q00426C75652Q012Q033Q0052656403053Q007072696E7403403Q00202Q3A205363726970742075736573205B556E64657267726F756E642057617220322E302041432064697361626C65725D204D61646520627920682Q7470732C03043Q005465616D03043Q007761726E034A3Q00202Q3A205544572D322E3020416E746943686561742044697361626C6572202Q3A20557365722069736E277420696E207465616D2C20576F6E7420612Q706C7920627970612Q7365722103263Q00202Q3A202857616974696E6720466F72205573657220746F204A6F696E205465616D3Q2E2903043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C03553Q00202Q3A2053752Q63652Q7366752Q6C792044697361626C656420416E746943686561742C20556E64657267726F756E642057617220322E302041432044697361626C6572204D61646520627920682Q7470733Q2E03553Q00202Q3A205544572D322E3020416E746943686561742044697361626C6572202Q3A204661696C656421204D61796265205573657228596F752920616C72656164792064697361626C656420416E746943686561743F00333Q0012143Q00013Q0020085Q00020020085Q00032Q000500013Q0002001214000200013Q00202Q000200020004001201000400054Q000900020004000200200800020002000600200D000100020007001214000200013Q00202Q000200020004001201000400054Q000900020004000200200800020002000800200D000100020007001214000200093Q0012010003000A4Q000300020002000100200800023Q000B2Q001F00020001000200061C000200250001000100040C3Q002500010012140002000C3Q0012010003000D4Q00030002000200010012140002000C3Q0012010003000E4Q00030002000200010012140002000F3Q002008000200020010001201000300114Q000300020002000100200800023Q000B2Q001F00020001000200060E0002001D00013Q00040C3Q001D0001001214000200123Q00060700033Q000100012Q00138Q000200020002000200060E0002002F00013Q00040C3Q002F0001001214000300093Q001201000400134Q000300030002000100040C3Q003200010012140003000C3Q001201000400144Q00030003000200012Q00043Q00013Q00013Q000F3Q0003043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503063Q004576656E747303063Q0052656D6F7465030A3Q0053656C665265706F727403073Q0044657374726F7903093Q00576F726B7370616365030E3Q0046696E6446697273744368696C6403043Q004E616D65030F3Q004C5F4F7074696D697A6174696F6E7303083Q0044697361626C65642Q0103073Q004D6F64756C6573030A3Q004D5F4E6F74696669657200203Q0012143Q00013Q00206Q0002001201000200034Q00093Q000200020020085Q00040020085Q00050020085Q000600206Q00072Q00033Q000200010012143Q00013Q0020085Q000800206Q00092Q001900025Q00200800020002000A2Q00093Q0002000200060E3Q001700013Q00040C3Q0017000100202Q00013Q00090012010003000B4Q000900010003000200060E0001001700013Q00040C3Q0017000100301E0001000C000D001214000100013Q00202Q000100010002001201000300034Q000900010003000200200800010001000E00200800010001000F00202Q0001000100072Q00030001000200012Q00043Q00017Q00", GetFEnv(), ...);
