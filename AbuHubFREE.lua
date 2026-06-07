--[[
Secured by AbubakrWxish
]]
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
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum == 2) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 5) then
							if (Enum == 4) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum > 6) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 11) then
						if (Enum <= 9) then
							if (Enum == 8) then
								Stk[Inst[2]] = Inst[3];
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
									if (Mvm[1] == 25) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum == 10) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 13) then
						if (Enum == 12) then
							do
								return;
							end
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 14) then
						do
							return;
						end
					elseif (Enum == 15) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
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
							if (Mvm[1] == 25) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					end
				elseif (Enum <= 24) then
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
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 22) then
						if (Enum == 21) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 23) then
						Stk[Inst[2]]();
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 28) then
					if (Enum <= 26) then
						if (Enum > 25) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum > 27) then
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					else
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					end
				elseif (Enum <= 30) then
					if (Enum == 29) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					else
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 31) then
					Stk[Inst[2]]();
				elseif (Enum > 32) then
					Stk[Inst[2]][Inst[3]] = Inst[4];
				else
					local A = Inst[2];
					Stk[A] = Stk[A](Stk[A + 1]);
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!433Q0003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203083Q00496E7374616E63652Q033Q006E657703093Q005363722Q656E47756903043Q004E616D65030F3Q0043682Q6F736553637269707447554903063Q00506172656E74030C3Q0057616974466F724368696C6403093Q00506C6179657247756903053Q004672616D6503043Q0053697A6503053Q005544696D32028Q00025Q00406F40026Q00694003083Q00506F736974696F6E026Q00E03F025Q00405FC0026Q0059C003103Q004261636B67726F756E64436F6C6F723303063Q00436F6C6F723303073Q0066726F6D524742026Q00394003063Q004163746976652Q0103093Q004472612Q6761626C6503083Q005549436F726E6572030C3Q00436F726E657252616469757303043Q005544696D026Q00284003093Q00546578744C6162656C026Q00F03F026Q0049C0026Q004440026Q00244003163Q004261636B67726F756E645472616E73706172656E637903043Q0054657874030E3Q0053637269707420487562207C203203043Q00466F6E7403043Q00456E756D030A3Q00476F7468616D426F6C6403083Q005465787453697A65026Q003440030A3Q0054657874436F6C6F7233025Q00E06F40025Q00C06240030E3Q005465787458416C69676E6D656E7403043Q004C656674030A3Q005465787442752Q746F6E026Q003E40026Q0044C0026Q00144003013Q0058026Q004940026Q00324003113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E656374031A3Q002Q39204E696768747320466F72657374207C2041627520487562033F3Q006C6F6164737472696E672867616D653A482Q74704765742822682Q7470733A2Q2F706173746562696E2E636F6D2F7261772F442Q307569796578222Q29282903153Q0045737020506C6179657273207C2041627520487562025Q00805640033F3Q006C6F6164737472696E672867616D653A482Q74704765742822682Q7470733A2Q2F706173746562696E2E636F6D2F7261772F31597A3677597730222Q29282903133Q0053686966744C6F636B207C2041627520487562025Q0040604003793Q006C6F6164737472696E672867616D653A482Q74704765742822682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F6D696E685265616C2F6D61696E532F726566732F68656164732F6D61696E2F4F746865725F5363726970742F53686966746C6F636B2E6C7561222Q29282900A73Q00124Q00013Q00201D5Q000200201D5Q000300122Q000100043Q00201D00010001000500121E000200064Q000200010002000200302100010007000800200500023Q000A00121E0004000B4Q000600020004000200100100010009000200122Q000200043Q00201D00020002000500121E0003000C4Q001A000400014Q000600020004000200122Q0003000E3Q00201D00030003000500121E0004000F3Q00121E000500103Q00121E0006000F3Q00121E000700114Q00060003000700020010010002000D000300122Q0003000E3Q00201D00030003000500121E000400133Q00121E000500143Q00121E000600133Q00121E000700154Q000600030007000200100100020012000300122Q000300173Q00201D00030003001800121E000400193Q00121E000500193Q00121E000600194Q00060003000600020010010002001600030030210002001A001B0030210002001C001B00122Q000300043Q00201D00030003000500121E0004001D4Q001A000500024Q000600030005000200122Q0004001F3Q00201D00040004000500121E0005000F3Q00121E000600204Q00060004000600020010010003001E000400122Q000300043Q00201D00030003000500121E000400214Q001A000500024Q000600030005000200122Q0004000E3Q00201D00040004000500121E000500223Q00121E000600233Q00121E0007000F3Q00121E000800244Q00060004000800020010010003000D000400122Q0004000E3Q00201D00040004000500121E0005000F3Q00121E000600253Q00121E0007000F3Q00121E0008000F4Q000600040008000200100100030012000400302100030026002200302100030027002800122Q0004002A3Q00201D00040004002900201D00040004002B0010010003002900040030210003002C002D00122Q000400173Q00201D00040004001800121E0005000F3Q00121E0006002F3Q00121E000700304Q00060004000700020010010003002E000400122Q0004002A3Q00201D00040004003100201D00040004003200100100030031000400122Q000400043Q00201D00040004000500121E000500334Q001A000600024Q000600040006000200122Q0005000E3Q00201D00050005000500121E0006000F3Q00121E000700343Q00121E0008000F3Q00121E000900344Q00060005000900020010010004000D000500122Q0005000E3Q00201D00050005000500121E000600223Q00121E000700353Q00121E0008000F3Q00121E000900364Q000600050009000200100100040012000500302100040027003700122Q000500173Q00201D00050005001800121E0006002F3Q00121E000700383Q00121E000800384Q00060005000800020010010004002E000500122Q0005002A3Q00201D00050005002900201D00050005002B0010010004002900050030210004002C003900122Q000500173Q00201D00050005001800121E000600383Q00121E000700383Q00121E000800384Q000600050008000200100100040016000500122Q000500043Q00201D00050005000500121E0006001D4Q001A000700044Q000600050007000200122Q0006001F3Q00201D00060006000500121E000700223Q00121E0008000F4Q00060006000800020010010005001E000600201D00050004003A00200500050005003B00060900073Q000100012Q00193Q00014Q001800050007000100060900050001000100012Q00193Q00024Q001A000600053Q00121E0007003C3Q00121E000800383Q00121E0009003D4Q00180006000900012Q001A000600053Q00121E0007003E3Q00121E0008003F3Q00121E000900404Q00180006000900012Q001A000600053Q00121E000700413Q00121E000800423Q00121E000900434Q00180006000900012Q000E3Q00013Q00023Q00013Q0003073Q0044657374726F7900044Q00047Q0020055Q00012Q001C3Q000200012Q000E3Q00017Q001D3Q0003083Q00496E7374616E63652Q033Q006E6577030A3Q005465787442752Q746F6E03043Q0053697A6503053Q005544696D32026Q00F03F026Q0034C0028Q00025Q0080414003083Q00506F736974696F6E026Q00244003043Q005465787403103Q004261636B67726F756E64436F6C6F723303063Q00436F6C6F723303073Q0066726F6D524742026Q004440030A3Q0054657874436F6C6F7233025Q00E06F4003043Q00466F6E7403043Q00456E756D030A3Q00476F7468616D426F6C6403083Q005465787453697A65026Q00304003083Q005549436F726E6572030C3Q00436F726E657252616469757303043Q005544696D026Q00204003113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E656374033A3Q00122Q000300013Q00201D00030003000200121E000400034Q000400056Q000600030005000200122Q000400053Q00201D00040004000200121E000500063Q00121E000600073Q00121E000700083Q00121E000800094Q000600040008000200100100030004000400122Q000400053Q00201D00040004000200121E000500083Q00121E0006000B3Q00121E000700084Q001A000800014Q00060004000800020010010003000A00040010010003000C3Q00122Q0004000E3Q00201D00040004000F00121E000500103Q00121E000600103Q00121E000700104Q00060004000700020010010003000D000400122Q0004000E3Q00201D00040004000F00121E000500123Q00121E000600123Q00121E000700124Q000600040007000200100100030011000400122Q000400143Q00201D00040004001300201D00040004001500100100030013000400302100030016001700122Q000400013Q00201D00040004000200121E000500184Q001A000600034Q000600040006000200122Q0005001A3Q00201D00050005000200121E000600083Q00121E0007001B4Q000600050007000200100100040019000500201D00040003001C00200500040004001D00060900063Q000100012Q00193Q00024Q00180004000600012Q000E3Q00013Q00013Q00013Q00030A3Q006C6F6164737472696E6700083Q00124Q00014Q000400016Q00023Q000200020006163Q000700013Q0004033Q000700012Q001A00016Q00170001000100012Q000E3Q00017Q00", GetFEnv(), ...);
