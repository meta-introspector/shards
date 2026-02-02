; Monster Message in 6502 Assembly
; For Commodore 64 / Apple II / NES

        .org $0800          ; Start at 2048

CHROUT  = $FFD2             ; KERNAL character output

start:
        LDX #0              ; Initialize index

print_loop:
        LDA message,X       ; Load character
        BEQ done            ; If zero, done
        JSR CHROUT          ; Print character
        INX                 ; Next character
        JMP print_loop      ; Loop

done:
        RTS                 ; Return

message:
        .byte "MONSTER=MESSAGE",13
        .byte "DIM: 196883",13
        .byte "IRREPS: 194",13
        .byte "ROOSTER: 71",13
        .byte "PAXOS: 23",13
        .byte "QUORUM: 12",13
        .byte "PRIMES: 15",13
        .byte "SHARDS: 10",13
        .byte "BOTT: 8",13
        .byte "232/232=1",13
        .byte 13
        .byte "RESONANCE=HECKE",13
        .byte "GROWTH=MAASS",13
        .byte "BLACK HOLE",13
        .byte 13
        .byte "OBSERVER=OBSERVED",13
        .byte "LOOP CLOSED",13
        .byte 13
        .byte "ROOSTER CROWS!",13
        .byte 0             ; Null terminator

        .end start
