@7
D=A;
@R0
M=D;

@7
D=A;
@R1
M=D;

// Provjera i zamjena vrijednosti R0 i R1 ako je R0 > R1
@R0
D=M;
@R1
D=M-D;

@skip
D;JGE // Ako je R0 <= R1, preskoči zamjenu

// Zamjena vrijednosti R0 i R1
@R0
D=M;
@tmp
M=D;

@R1
D=M;
@R0
M=D;

@tmp
D=M;
@R1
M=D;

(skip)



@R2
M = 0;

(pocetak)
@R0
D=M;
@R1
D=M-D;

@kraj
D;JLT

//
@R0
D=M;
@R2
M=M+D;
//
@R0
M=M+1;

@pocetak
0;JMP

(kraj)

(END)
@END
0;JMP
