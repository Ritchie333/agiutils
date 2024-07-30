program xvol;
{
   Program to extract individual files from an AGI version 3 VOL file.

   This is an old version written in pascal that I have decided to keep with
   this archive in case someone can make use of it. It only supports the
   basic extraction facilities of earlier XV3 version though.
}

uses Dos;

const
 fileNames : array[1..4] of string[9] = (
  'LOGIC.', 'PICTURE.', 'VIEW.', 'SOUND.'
 );
 MAXBITS = 12;
 TABLE_SIZE = 18041;
 START_BITS = 9;

type
 prefix_code_array = array[0..TABLE_SIZE] of word;
 append_character_array = array[0..TABLE_SIZE] of char;
 prefix_code_type = ^prefix_code_array;
 append_character_type = ^append_character_array;
 FileType = file of char;

var
 BITS, MAX_VALUE, MAX_CODE : integer;
 prefix_code : prefix_code_type;
 append_character : append_character_type;
 input_bit_count : integer;
 input_bit_buffer : longint;

function SetBITS(Value:integer):boolean;
begin
 if (Value = MAXBITS) then
  SetBITS := TRUE
 else
  begin
   BITS := Value;
   MAX_VALUE := (1 SHL BITS) - 1;
   MAX_CODE := MAX_VALUE - 1;
   SetBITS := FALSE;
  end;
end;

function decode_string(AString:string; code: word) :string;
var
 i : integer;
begin
 i := 0;
 While (code > 255) do
 begin
  AString := concat(AString, append_character^[code]);
  code := prefix_code^[code];
  i := i + 1;
  if (i > 4000) then
  begin
   WriteLn('Fatal error during code expansion.');
   Halt(1);
  end;
 end;
 AString := concat(AString, Chr(ord(code)));
 decode_string := AString;
end;

function input_code(var input:FileType) : word;
var
 return_value:word;
 CharacterInput : char;
 AWord:word;
begin
 While ((input_bit_count <= 24) and (not EOF(input))) do
 begin
  Read(input, CharacterInput);
  AWord := ORD(CharacterInput);
  input_bit_buffer := input_bit_buffer or (AWord SHL input_bit_count);
  input_bit_count := input_bit_count + 8;
 end;
 return_value := (input_bit_buffer and $7FFF) MOD (1 SHL BITS);
 input_bit_buffer := input_bit_buffer SHR BITS;
 input_bit_count := input_bit_count - BITS;
 if EOF(input) then return_value := MAX_VALUE;
 input_code := return_value;
end;

procedure expand(var input, output : FileType; fileLength : word);
var
 next_code, new_code, old_code : word;
 character, counter, index : integer;
 AString : string;
 AChar :char;
 BITSFull : boolean;
 i : integer;
begin
 BITSFull := SetBITS(START_BITS);   {Set initial value of BITS}

 next_code := 257;                {Next available code to define. SIERRA start at 257}
                                  {256 is apparently the table flush code}
 counter := 0;                    {counter is a pacifier}
 WriteLn('Expanding...');

 old_code := input_code(input);   {Read in the first code.}
 AChar := chr(ord(old_code));
 character := old_code;           {Initialise the character variable.}
 new_code := input_code(input);

 While (filepos(output) < fileLength) do
 begin

  if (counter = 1000) then    { Make it look like somethings being done }
  begin
   counter := 0;
   Write('*');
  end;
  counter := counter + 1;

  if (new_code = $100) then   { Restart LZW process }
  begin

   next_code := 258;
   BITSFull := SetBITS(START_BITS);
   old_code := input_code(input);   {Read in the first code.}
   AChar := chr(ord(old_code));
   character := old_code;           {Initialise the character variable.}
   Write(output, AChar);            {Send out the first code.}
   new_code := input_code(input);

  end
  else
  begin

   if (new_code >= next_code) then
    AString := decode_string(Chr(character), old_code)
   else
    AString := decode_string('', new_code);

   character := ord(AString[length(AString)]);
   for index := length(AString) downto 1 do
    Write(output, AString[index]);

   if (next_code > MAX_CODE) then
    BITSFull := SetBITS(BITS + 1);

   prefix_code^[next_code] := old_code;
   append_character^[next_code] := Chr(character);
   next_code := next_code + 1;
   old_code := new_code;
   AString := '';
   new_code := input_code(input);

  end;
 end;
end;

function findGameSig: string;
var
   DirInfo: SearchRec;
   dirString: string;
   volString: string;
begin
   dirString := '';
   volString := '';

   FindFirst('*.?', Archive, DirInfo);
   while DosError = 0 do
   begin
      if (pos('DIR', DirInfo.Name) > 1) then
         dirString := copy(DirInfo.Name, 1, pos('DIR', DirInfo.Name)-1);
      if (pos('VOL.0', DirInfo.Name) > 1) then
         volString := copy(DirInfo.Name, 1, pos('VOL.0', DirInfo.Name)-1);
      FindNext(DirInfo);
   end;

   if ((volString = dirString) and (volString <> '')) then
      findGameSig := volString
   else
      findGameSig := '';
end;

procedure extractFile(agiFileType, fileNum : integer);
var
   gameSig, dirFileName, volFileName, volFileNum: string;
   dirFile, volFile, tempFile : file of byte;
   dirOffsetLo, dirOffsetHi, firstByte, secondByte, thirdByte: byte;
   fLenHi, fLenLo, filebyte, decompLo, decompHi, compType : byte;
   fLen, dirFilePos, decompSize : word;
   volFilePos, calcLongInt: longint;
   transferChar : char;
   sierraFile, dumpFile : FileType;
   dumpFileNum, dumpFileName : string;
begin
   gameSig := findGameSig;
   if (gameSig = '') then
   begin
      writeln('Error locating version 3 game files!');
      writeln('Make sure you run XV3 in a directory');
      writeln('containing a game which uses AGI v3.');
      halt;
   end;

   dirFileName := concat(gameSig, 'DIR');
   {$I-}
   assign(dirFile, dirFileName);
   reset(dirFile);
   {$I+}
   if (IOResult = 0) then
   begin
      seek(dirFile, (agiFileType * 2));
      read(dirFile, dirOffsetLo, dirOffsetHi);
      seek(dirFile, ((dirOffsetHi * 256) + dirOffsetLo) + (fileNum*3));
      read(dirFile, firstByte, secondByte, thirdByte);
      close(dirFile);

      if ((firstByte = $FF) and (secondByte = $FF) and (thirdByte = $FF)) then
      begin
         writeln('File doesn''t exist');
         halt;
      end
      else
      begin
         calcLongInt := firstByte;
         volFilePos := (calcLongInt and $F) shl 16;
         calcLongInt := secondByte;
         volFilePos := volFilePos + (calcLongInt shl 8);
         calcLongInt := thirdByte;
         volFilePos := volFilePos + calcLongInt;
         str((firstByte and $F0) shr 4, volFileNum);
         volFileName := concat(gameSig, 'VOL.', volFileNum);

         {$I-}
         assign(volFile, volFileName);
         reset(volFile);
         {$I+}
         if (IOResult <> 0) then
         begin
            writeln('Error opening vol file : ',volFileName);
            halt;
         end;

         seek(volFile, volFilePos + 2);
         read(volFile, compType, decompLo, decompHi, fLenLo, fLenHi);
         decompSize := (decompHi * 256) + decompLo;
         fLen := (fLenHi * 256) + fLenLo;

         {$I-}
         assign(tempFile, 'TEMP');
         rewrite(tempFile);
         {$I+}
         if (IOResult <> 0) then
         begin
            writeln('Error opening TEMP file.');
            halt;
         end;

         for dirFilePos := 0 to fLen - 1 do
         begin
            read(volFile, fileByte);
            write(tempFile, fileByte);
         end;
         close(tempFile);
         close(volFile);


         { DECOMPRESS TEMP FILE }

         input_bit_buffer := 0;
         input_bit_count := 0;

         NEW(prefix_code);
         NEW(append_character);
         if (prefix_code = nil) or (append_character = nil) then
         begin
            WriteLn('Fatal error allocating table space!');
            Halt(1);
         end;

         assign(sierraFile, 'TEMP');
         reset(sierraFile);

         str(fileNum, dumpFileNum);
         dumpFileName := concat(fileNames[agiFileType + 1], dumpFileNum);
         {$I-}
         assign(dumpFile, dumpFileName);
         rewrite(dumpFile);
         {$I+}
         if (IOResult <> 0) then
         begin
            writeln('Error opening dump file : ',dumpFileName);
            halt;
         end;

         if (((compType and $80) <> $80) and (decompSize != fLen)) then
            expand(sierraFile, dumpFile, decompSize)
         else
            while (not eof(sierraFile)) do
            begin
               read(sierraFile, transferChar);
               write(dumpFile, transferChar);
            end;

         close(sierraFile);
         close(dumpFile);
         DISPOSE(prefix_code);
         DISPOSE(append_character);
      end;
   end
   else
   begin
      writeln('Error opening DIR file : ',dirFileName);
      halt;
   end;
end;

var
   fileNum, code : integer;
   option : string;
begin

   if (paramcount < 2) then
   begin
      writeln('Usage: xv3 -l logicnumber');
      writeln('       xv3 -s soundnumber');
      writeln('       xv3 -v viewnumber');
      writeln('       xv3 -p picturenumber');
   end
   else
   begin

      option := paramstr(1);

      if (option[1] = '-') then
      begin

	       val(paramstr(2), fileNum, code);
         if (code <> 0) then
         begin
            writeln('Error at position : ',code);
            halt;
         end;

	       if (fileNum >= 0) then
	       begin

	          case (option[2]) of

	             'l': extractFile(0, fileNum);
	             's': extractFile(3, fileNum);
	             'v': extractFile(2, fileNum);
	             'p': extractFile(1, fileNum);

	          else
               writeln('Invalid option : ', paramstr(1));
	          end;

	       end
	       else
	          writeln('File number must be a postive number.');
      end
      else
	       writeln('Invalid option : ', paramstr(1));

   end;

end.
