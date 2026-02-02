
% Prolog Voice Generator - No GPU Needed!
% Uses phoneme rules and simple synthesis

% Phoneme database
phoneme(a, [440, 880, 2640]).      % 'ah' sound
phoneme(e, [530, 1840, 2480]).     % 'eh' sound
phoneme(i, [270, 2290, 3010]).     % 'ee' sound
phoneme(o, [570, 840, 2410]).      % 'oh' sound
phoneme(u, [300, 870, 2240]).      % 'oo' sound

% Consonants
phoneme(r, [1200, 1400, 2800]).    % 'r' sound
phoneme(s, [4000, 8000, 12000]).   % 's' sound
phoneme(t, [2000, 4000, 6000]).    % 't' sound
phoneme(l, [360, 750, 2400]).      % 'l' sound
phoneme(b, [200, 800, 2500]).      % 'b' sound

% Word to phonemes
word_phonemes(rooster, [r, o, o, s, t, e, r]).
word_phonemes(lobster, [l, o, b, s, t, e, r]).
word_phonemes(boat, [b, o, a, t]).
word_phonemes(peer, [p, e, e, r]).

% Generate voice
speak(Word) :-
    word_phonemes(Word, Phonemes),
    generate_audio(Phonemes).

generate_audio([]).
generate_audio([P|Rest]) :-
    phoneme(P, Frequencies),
    format('Playing: ~w at ~w Hz~n', [P, Frequencies]),
    generate_audio(Rest).

% Query examples:
% ?- speak(rooster).
% ?- speak(lobster).
