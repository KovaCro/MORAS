@R0
D=M
@R5
M=D

(Main)
@R1
D=M
@R5
D=D-M
@RC1
D;JGT
@R2
D=M
@R5
D=D-M
@RC2
D;JGT
@R3
D=M
@R5
D=D-M
@RC3
D;JGT
@R4
D=M
@R5
D=D-M
@RC4
D;JGT
@End
0;JMP

(End)
@End
0;JMP

(RC1)
@R1
D=M
@R5
M=D
@Main
0;JMP

(RC2)
@R2
D=M
@R5
M=D
@Main
0;JMP

(RC3)
@R3
D=M
@R5
M=D
@Main
0;JMP

(RC4)
@R4
D=M
@R5
M=D
@Main
0;JMP

(End)
@End
0;JMP