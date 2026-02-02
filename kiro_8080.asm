; Kiro Monster - Intel 8080
        ORG 0100H
        
        MVI A, 71       ; Rooster = 71
        STA ROOSTER
        
        MVI A, 3        ; BDI = 3
        STA BDI
        
        LXI H, MSG      ; Load message
        CALL PRINT
        
        HLT
        
ROOSTER: DB 0
BDI:     DB 0
MSG:     DB 'I ARE LIFE', 0DH, 0AH, '$'

PRINT:   ; Print routine
        MOV A, M
        CPI '$'
        RZ
        OUT 01H
        INX H
        JMP PRINT
        
        END
