\ ChaCha quarter round
\   1.  a += b; d ^= a; d <<<= 16;
\   2.  c += d; b ^= c; b <<<= 12;
\   3.  a += b; d ^= a; d <<<= 8;
\   4.  c += d; b ^= c; b <<<= 7;

\ Use HEX for everything
HEX

\ Setup ENDIF as an alias for THEN
: ENDIF POSTPONE THEN ; IMMEDIATE


\ Rotate x left by n bits
: rotl ( x n -- x )
        dup 0x20 < if
        2dup 0x20 swap - rshift rot rot lshift or
        then ;

: qr ( a b c d -- a b c d )
        2>r swap over + swap 2r>       \ a += b
        rot rot 2>r over xor 2r> rot   \ d ^= a
        0x10 rotl                      \ d <<<= 16
        swap over + swap               \ c += d
        >r swap over xor swap r>       \ b ^= c
        2>r 0xC rotl 2r>               \ b <<<= 12
        2>r swap over + swap 2r>       \ a += b
        rot rot 2>r over xor 2r> rot   \ d ^= a
        0x8 rotl                       \ d <<<= 8
        swap over + swap               \ c += d
        >r swap over xor swap r>       \ b ^= c
        2>r 0x7 rotl 2r> ;             \ b <<<= 7

\ Quarter round test vectors from RFC 7539
\  o  a = 0x11111111
\  o  b = 0x01020304
\  o  c = 0x9b8d6f43
\  o  d = 0x01234567

: qrtest ( -- )
        cr
        0x11111111 0x01020304 0x9b8d6f43 0x01234567 
        cr
        qr U. U. U. U. ;
        
\ results
\  o  a = 0xea2a92f4
\  o  b = 0xcb1cf8ce
\  o  c = 0x4581472e
\  o  d = 0x5881c4bb

\ Create a arrays to hold the chacha state & working state
variable chachastate 0xF cells allot
variable workingstate 0xF cells allot
\ And arrays to store the key, counter, and nonce
variable keystore 0x8 cells allot
variable noncestore 0x6 cells allot
variable counterstore 0x2 cells allot
variable xblockstore 0xF cells allot
\ Read cell n via 
\ chachastate n cells + @
\ write to cell n via
\ value chachastate n cells + !

\ That takes too much work, so define the word ccs to get the address
\ to get the value at index n:
\ n ccs @
\ to set the value at index n:
\ n ccs !
: ccs ( n -- addr ) cells chachastate + ;
: wks ( n -- addr ) cells workingstate + ;
: kss ( n -- addr ) cells keystore + ;
: nss ( n -- addr ) cells noncestore + ;
: ctr ( n -- addr ) cells counterstore + ;
: xbl ( n -- addr ) cells xblockstore + ;

\ Setup the state from the stack. The first 4 words are constant. 
\ The first four words (0-3) are constants: 0x61707865, 0x3320646e,
\      0x79622d32, 0x6b206574.
: sleeveless ( -- )
        \ Nothing-up-my-sleeve numbers. "expand 32-byte k"
        0x61707865 0x0 ccs ! 
        0x3320646E 0x1 ccs ! 
        0x79622D32 0x2 ccs ! 
        0x6B206574 0x3 ccs ! ;

: setup ( nonce1 nonce0 ctr1 ctr0 key7 key6 key5 key4 key3 key2 key1 key0 -- )
        sleeveless
        \ Key goes here. 
        0x4 ccs ! 0x5 ccs ! 0x6 ccs ! 0x7 ccs !
        0x8 ccs ! 0x9 ccs ! 0xA ccs ! 0xB ccs !
        \ Counter goes here
        0xC ccs ! 0xD ccs ! 
        \ Nonce goes here
        0xE ccs ! 0xF ccs ! ;
        
: ietfsetup ( nonce2 nonce1 nonce0 ctr0 key7 key6 key5 key4 key3 key2 key1 key0 -- )
        \ Same as normal, only the stack effect is different due to the differing
        \   counter and nonce lengths.
        setup ;

: xsetup ( nonce5 nonce4 nonce3 nonce2 nonce1 nonce0 key7 key6 key5 key4 key3 key2 key1 key0 -- )
        sleeveless
        \ Key goes here
        0x4 ccs ! 0x5 ccs ! 0x6 ccs ! 0x7 ccs !
        0x8 ccs ! 0x9 ccs ! 0xA ccs ! 0xB ccs !
        \ Nonce goes here. Counter added when init called.
        0xC ccs ! 0xD ccs ! 0xE ccs ! 0xF ccs ! ;
        
\ Get the key from the state after initial setup only!
: key_ccs->kss ( -- )
        0x4 ccs @ 0x0 kss !
        0x5 ccs @ 0x1 kss !
        0x6 ccs @ 0x2 kss !
        0x7 ccs @ 0x3 kss !
        0x8 ccs @ 0x4 kss !
        0x9 ccs @ 0x5 kss !
        0xA ccs @ 0x6 kss !
        0xB ccs @ 0x7 kss ! ;
        
\ Set the key in the state from storage.
: key_kss->ccs ( -- )
        0x0 kss @ 0x4 ccs !
        0x1 kss @ 0x5 ccs !
        0x2 kss @ 0x6 ccs !
        0x3 kss @ 0x7 ccs !
        0x4 kss @ 0x8 ccs !
        0x5 kss @ 0x9 ccs !
        0x6 kss @ 0xA ccs !
        0x7 kss @ 0xB ccs ! ;
 
\ 3 nonce saving / restoring function pairs. Use after initial setup to store the nonce.
\ For default ChaCha20. 64-bit counter, 64-bit nonce
: nonce_ccs->nss ( -- )
        0xE ccs @ 0x0 nss !
        0xF ccs @ 0x1 nss ! 
        \ For safety, zero out the rest of the nonce storage memory.
        0 0x2 nss ! 0 0x3 nss ! 0 0x4 nss ! 0 0x5 nss ! ;
     
: nonce_nss->ccs ( -- )
        0x1 nss @ 0x0 nss @ 
        0xE ccs ! 0xF ccs ! ;
        
\ For the IETF version of ChaCha20. 32-bit counter, 96-bit nonce
: ietfnonce_ccs->nss ( -- )
        0xD ccs @ 0x0 nss !
        0xE ccs @ 0x1 nss !
        0xF ccs @ 0x2 nss !
        \ For safety, zero out the rest of the nonce storage memory
        0 0x3 nss ! 0 0x4 nss ! 0 0x5 nss ! ;

: ietfnonce_nss->ccs ( -- )
        0x2 nss @ 0x1 nss @ 0x0 nss @
        0xD ccs ! 0xE ccs ! 0xF ccs ! ;

\ For the XChaCha20 version. 64-bit counter, 192-bit Nonce. 2 Functions, due to 
\  the way XChaCha20 works.     
: xnonce_ccs->nss1 ( -- )
        0xC ccs @ 0x0 nss !
        0xD ccs @ 0x1 nss !
        0xE ccs @ 0x2 nss !
        0xF ccs @ 0x3 nss ! 
        \ For safety, zero out the rest of the nonce storage memory
        0 0x4 nss ! 0 0x5 nss ! ;
: xnonce_ccs->nss2 ( -- )
        0xE ccs @ 0x4 nss ! 
        0xF ccs # 0x5 nss ! ;
        
\ Debugging only
: xnonce_nss->stack ( -- nonce5 nonce4 nonce3 nonce2 nonce1 nonce0 )
        0x5 nss @ 0x4 nss @ 0x3 nss @ 0x2 nss @ 0x1 nss @ 0x0 nss @ ;

\ same        
: xgetnonce2 ( -- nonce5 nonce4 )
        0x5 nss @ 0x4 nss @ ;
      
: xnonce_nss->ccs ( -- )
        0x5 nss @ 0x4 nss @
        0xE ccs ! 0xF ccs ! ;
        

\ And some functions to save and restore the counter.
: counter_ccs->ctr ( -- )
        0xC ccs @ 0x0 ctr !
        0xD ccs @ 0x1 ctr ! ;
        
: counter_ctr->stack ( -- ctr0 ctr1 )
        0x0 ctr @ 0x1 ctr @ ;
        
: counter_ctr->ccs ( -- )
        0x0 ctr @ 0xC ccs !
        0x1 ctr @ 0xD ccs ! ;
      
\ IETF version has only a 32-bit counter      
: ietfcounter_ccs->ctr ( -- )
        0xC ccs @ 0x0 ctr ! ;
        
: ietfcounter_ctr->stack ( -- ctr )
        0x0 ctr @ ;
        
: ietfcounter_ctr->ccs ( -- )
        0x0 ctr @ 0xC ccs ! ;

\ XChaCha counter is the same as normal, just done after the X round       

: xblock_wks->xbl
        0xB wks @ 0x0 xbl ! 
        0xA wks @ 0x1 xbl ! 
        0x9 wks @ 0x2 xbl ! 
        0x8 wks @ 0x3 xbl !
        0x7 wks @ 0x4 xbl ! 
        0x6 wks @ 0x5 xbl !
        0x5 wks @ 0x6 xbl ! 
        0x4 wks @ 0x7 xbl ! ;

: xblock_xbl->ccs
        0x0 xbl @ 0x4 ccs !
        0x1 xbl @ 0x5 ccs !
        0x2 xbl @ 0x6 ccs !
        0x3 xbl @ 0x7 ccs !
        0xC xbl @ 0x8 ccs !
        0xD xbl @ 0x9 ccs !
        0xE xbl @ 0xA ccs !
        0xF xbl @ 0xB ccs ! ;

\ Print out the current state
: printstate ( -- )
        cr cr
        0x10 0 ?do
                i ccs @ U.
        loop ;
        
\ Print out the current working state, for debugging / demo
: printworking ( -- )
        cr cr
        0x10 0 ?do
                i wks @ U.
        loop ;
        
\ Copy chachastate to workingstate
: copyccs ( -- )
        0x10 0 ?do
                i ccs @ 
                i wks !
        loop ;

\ chachastate += workingstate
: updatestate ( -- )
        0x10 0 ?do
                i wks @ 
                i ccs @ 
                + i ccs !
        loop ;

\ ChaCha State
\ 0 1 2 3
\ 4 5 6 7
\ 8 9 A B
\ C D E F
        
\ ChaCha20 inner block function
\  Starts out with 4 quarter rounds, operating on the columns of the state
\   1.  QUARTERROUND ( 0, 4, 8, C)
\   2.  QUARTERROUND ( 1, 5, 9, D)
\   3.  QUARTERROUND ( 2, 6, A, E)
\   4.  QUARTERROUND ( 3, 7, B, F)
\  Then does 4 more quarter rounds, operating on the diagonals of the state
\   5.  QUARTERROUND ( 0, 5, A, F)
\   6.  QUARTERROUND ( 1, 6, B, C)
\   7.  QUARTERROUND ( 2, 7, 8, D)
\   8.  QUARTERROUND ( 3, 4, 9, E)
: innerblock ( -- )
        \ First do the column rounds
        0x0 wks @ 0x4 wks @ 0x8 wks @ 0xC wks @ qr
        0xC wks ! 0x8 wks ! 0x4 wks ! 0x0 wks !
        0x1 wks @ 0x5 wks @ 0x9 wks @ 0xD wks @ qr
        0xD wks ! 0x9 wks ! 0x5 wks ! 0x1 wks ! 
        0x2 wks @ 0x6 wks @ 0xA wks @ 0xE wks @ qr
        0xE wks ! 0xA wks ! 0x6 wks ! 0x2 wks ! 
        0x3 wks @ 0x7 wks @ 0xB wks @ 0xF wks @ qr
        0xF wks ! 0xB wks ! 0x7 wks ! 0x3 wks ! 
        \ First round done
        \ Then do the diagonal rounds
        0x0 wks @ 0x5 wks @ 0xA wks @ 0xF wks @ qr
        0xF wks ! 0xA wks ! 0x5 wks ! 0x0 wks ! 
        0x1 wks @ 0x6 wks @ 0xB wks @ 0xC wks @ qr
        0xC wks ! 0xB wks ! 0x6 wks ! 0x1 wks ! 
        0x2 wks @ 0x7 wks @ 0x8 wks @ 0xD wks @ qr
        0xD wks ! 0x8 wks ! 0x7 wks ! 0x2 wks ! 
        0x3 wks @ 0x4 wks @ 0x9 wks @ 0xE wks @ qr 
        0xE wks ! 0x9 wks ! 0x4 wks ! 0x3 wks ! ;
        \ Second round done

\ The ChaCha20 block function
: chachablock ( -- )
        copyccs
        \ 20 rounds, 10 column and 10 diagonal
        0xA 0 ?do 
                innerblock
        loop
        updatestate ;
        
: chachablock_noupdate ( -- )
        copyccs
        \ 20 rounds, 10 column and 10 diagonal
        0xA 0 ?do
                innerblock
        loop ; \ Not updating state
        
\   For a test vector, we will use the following inputs to the ChaCha20
\   block function:
\
\   o  Key = 00:01:02:03:04:05:06:07:08:09:0a:0b:0c:0d:0e:0f:10:11:12:13:
\      14:15:16:17:18:19:1a:1b:1c:1d:1e:1f.  The key is a sequence of
\      octets with no particular structure before we copy it into the
\      ChaCha state.
\
\   o  Nonce = (00:00:00:09:00:00:00:4a:00:00:00:00)
\
\   o  Block Count = 1.
\
\   After setting up the ChaCha state, it looks like this:
\
\   ChaCha state with the key setup.
\
\    61707865  3320646e  79622d32  6b206574
\    03020100  07060504  0b0a0908  0f0e0d0c
\    13121110  17161514  1b1a1918  1f1e1d1c
\    00000001  09000000  4a000000  00000000
\       
\   ChaCha state at the end of the ChaCha20 operation
\ 
\    e4e7f110  15593bd1  1fdd0f50  c47120a3
\    c7f4d1c7  0368c033  9aaa2204  4e6cd4c3
\    466482d2  09aa9f07  05d7c214  a2028bd9
\    d19c12b5  b94e16de  e883d0cb  4e3c50a2

( nonce2 nonce1 nonce0 ctr0 key7 key6 key5 key4 key3 key2 key1 key0 -- )       
: blocktest ( -- )
        0x00000000 0x4A000000 0x09000000 \ Nonce
        0x00000001 \ Counter
        0x1f1e1d1c 0x1b1a1918 0x17161514 0x13121110
        0x0f0e0d0c 0x0b0a0908 0x07060504 0x03020100
        ietfsetup chachablock printstate ;

\ 3 setup words, 1 for each supported variant

\ DJB standard version setup is simple. 64-bit counter and nonce.
: chachainit ( nonce counter key -- )
        setup key_ccs->kss nonce_ccs->nss counter_ccs->ctr 
        printstate 
        chachablock
        printstate ;
        
\ IETF is similarly simple.
: ietfinit ( nonce counter key -- )
        ietfsetup key_ccs->kss ietfnonce_ccs->nss ietfcounter_ccs->ctr 
        printstate 
        chachablock
        printstate ;

\ XChaCha20 has a more complicated setup.
: xinit ( nonce key -- )
        \ Setup the first block
        xsetup key_ccs->kss xnonce_ccs->nss1
        \ One run of the inner block function, but without adding working state 
        \   to the state
        chachablock_noupdate
        \ Now get the updated blocks from the working state and save them
        xblock_wks->xbl
        \ The last 2 nonce blocks should already be on the stack
        sleeveless 
        0x4 nss ! 0x5 nss ! \ Store the last 2 words of the nonce into the state
        xnonce_ccs->nss2 \ Save them
        0 0x0 ctr ! 0 0x1 ctr ! \ Initialize counter to zero
        counter_ctr->ccs \ Store the counter in the state
        printstate 
        chachablock
        printstate ;
        
: inccounter
        swap
        dup
        0xFFFFFFFF
        = if
                swap
                1 d+
        else
                1 + swap
        endif ;

\ 3 usage words, 1 for each supported variant.
: chachastream ( -- )
        sleeveless \ Reset the first 4 bytes
        nonce_nss->ccs \ Reset the nonce
        key_kss->ccs \ Reset the key
        counter_ctr->stack
        inccounter \ Check for overflow and increment the counter
        0x1 ctr ! 0x0 ctr ! \ Store the counter
        counter_ctr->ccs \ Set the counter in the ChaCha state
        printstate
        chachablock \ Run the block function
        printstate ;
       
: ietfstream ( -- )
        sleeveless \ Reset the first 4 bytes
        ietfnonce_nss->ccs \ Reset the nonce
        key_kss->ccs \ Reset the key
        ietfcounter_ctr->stack 1 + 0x0 ctr ! \ Increment the counter
        ietfcounter_ctr->ccs \ Set the counter in the ChaCha state
        cr cr
        printstate
        chachablock \ Run the block function
        cr cr
        printstate ;
        
: xchachastream ( -- )
        sleeveless \ Reset the first 4 bytes
        xnonce_nss->ccs \ Reset the nonce 
        xblock_xbl->ccs \ Get the saved blocks
        counter_ctr->stack 
        inccounter \ Check for overflow and increment the counter
        0x1 ctr ! 0x0 ctr ! \ Store the counter
        counter_ctr->ccs \ Set the counter in the ChaCha state
        printstate
        chachablock \ Run the block function
        printstate ;

: chachatest ( -- )
        cr cr
        \ First block setup:
        \ 61707865 3320646e 79622d32 6b206574
        \ 00000000 00000000 00000000 00000000
        \ 00000000 00000000 00000000 00000000
        \ 00000000 00000000 00000000 00000000
        \ First block after block operation: 
        \ ade0b876 903df1a0 e56a5d40 28bd8653
        \ b819d2bd 1aed8da0 ccef36a8 c70d778b
        \ 7c5941da 8d485751 3fe02477 374ad8b8
        \ f4b8436a 1ca11815 69b687c3 8665eeb2
        ( nonce1 nonce0 ctr1 ctr0 key7 key6 key5 key4 key3 key2 key1 key0 -- )
        0x00000000 0x00000000 \ Nonce
        0x00000000 0x00000000 \ Counter
        0x00000000 0x00000000 0x00000000 0x00000000
        0x00000000 0x00000000 0x00000000 0x00000000
        chachainit
        chachastream cr cr ;

: ietftest ( -- )
        cr cr
        \ First block setup:
        \     61707865  3320646e  79622d32  6b206574
        \     03020100  07060504  0b0a0908  0f0e0d0c
        \     13121110  17161514  1b1a1918  1f1e1d1c
        \     00000001  00000000  4a000000  00000000
        \ First block after block operation:
        \     f3514f22  e1d91b40  6f27de2f  ed1d63b8
        \     821f138c  e2062c3d  ecca4f7e  78cff39e
        \     a30a3b8a  920a6072  cd7479b5  34932bed
        \     40ba4c79  cd343ec6  4c2c21ea  b7417df0
        \ Second block setup:
        \     61707865  3320646e  79622d32  6b206574
        \     03020100  07060504  0b0a0908  0f0e0d0c
        \     13121110  17161514  1b1a1918  1f1e1d1c
        \     00000002  00000000  4a000000  00000000
        \     40ba4c79  cd343ec6  4c2c21ea  b7417df0
        \ Second block after block operation:
        \     9f74a669  410f633f  28feca22  7ec44dec
        \     6d34d426  738cb970  3ac5e9f3  45590cc4
        \     da6e8b39  892c831a  cdea67c1  2b7e1d90
        \     037463f3  a11a2073  e8bcfb88  edc49139
         0x00000000 0x4A000000 0x00000000 \ Nonce
         0x00000001 \ Nonce
         0x1f1e1d1c 0x1b1a1918 0x17161514 0x13121110 \ key part 1
         0x0f0e0d0c 0x0b0a0908 0x07060504 0x03020100 \ key part 2
         ietfinit
         ietfstream cr cr ;
         
: xchachatest ( -- )
        cr cr
        \ First block setup:
        \ 61707865 3320646e 79622d32 6b206574
        \ 00000000 00000000 00000000 00000000
        \ 00000000 00000000 00000000 00000000
        \ 00000000 00000000 00000000 00000000
        \ First block after block operation: 
        \ ade0b876 903df1a0 e56a5d40 28bd8653
        \ b819d2bd 1aed8da0 ccef36a8 c70d778b
        \ 7c5941da 8d485751 3fe02477 374ad8b8
        \ f4b8436a 1ca11815 69b687c3 8665eeb2
        ( nonce5 nonce4 nonce3 nonce2 nonce1 nonce0 ctr1 ctr0 key7 key6 key5 key4 key3 key2 key1 key0 -- )
        0x00000000 0x00000000 0x00000000 0x00000000 0x00000000 0x00000000 \ Nonce
        0x00000000 0x00000000 \ Counter
        0x00000000 0x00000000 0x00000000 0x00000000 \ Key part 1
        0x00000000 0x00000000 0x00000000 0x00000000 \ Key part 2
        xinit
        xchachastream cr cr ;