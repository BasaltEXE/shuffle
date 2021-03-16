## Motivation

Ein Stapel mit 52 Spielkarten ist erst nach sechs bis sieben Bogenmischdurchläufen gut durchmischt.
Mischmaschinen sind entweder teuer oder unzuverlässig.
Meine Idee war es eine App zu entwickeln mit der man Spielkarten schnell und gründlich mischen kann.

## Ansatz

Zunächst wird jede Karte im Stapel zufällig entweder einem Spieler oder deren Position im Talon zugeordnet.
Im nächsten Schritt werden aus dieser Zuordnung, in Runden unterteilte, Anweisungen für den Kartengeber generiert, die auf dem Smartphone angezeigt werden.
Nach dem Abarbeiten der Anweisungen habe alle Spieler ihre Karten und alle Karten im Talon befinden sich an ihrer zugeordneten Position.

## Anweisungen

Zu Beginn einer Runde hält der Kartengeber alle noch nicht ausgeteilten Karten in der Hand.
Von diesem Stapel wird der Reihe nach die oberste Karte abgehoben und laut Anweisung auf einen der acht an das Smartphone angrenzenden Stapel gelegt.
Der jeweilige Stapel kann auch einem Spieler ausgehändigt werden.
Die Runde endet, wenn alle Karten abgelegt und die verbleibenden Stapel auf dem Tisch im Uhrzeigersinn aufgenommen wurden.

##  Knotenfärbung

Wir beschränken uns im Folgenden auf das Verteilen der Hände an die Spieler.
Das Sortieren des Talons funktioniert ähnlich.

Wir betrachten den Graph dessen Knoten die Spieler sind.
Wir ordnen jedem Spieler das Intervall zu dessen Endpunkte die Position des ersten bzw. letzten Auftretens im Kartenstapel sind.
Zwei Spieler sind benachbart, falls ihre Intervalle nicht disjunkt sind.
Der resultierende Graph ist ein Intervallgraph dessen chromatische Zahl mit der kleinsten Anzahl an Stapeln übereinstimmt mit der man alle Hände innerhalb einer Runde austeilen kann.

In jeder Runde bestimmt man also zunächst die chromatische Zahl und eine gültige Färbung des Intervallgraphen.
Stehen nicht genügend Stapel zur Verfügung berechnen wir stattdessen eine ungültige Färbung, die die chromatische Zahl der nächsten Runde reduziert.

Aus der Färbung lassen sich nun die Anweisungen generieren.

##  Verifikation

Sei `Player` der Typ der Spieler.
Den im letzten Abschnitt beschriebenen Intervallgraph kann man als Liste `x` von Tupel [`Opcode * Player`](../01475aea5b02484677b4a155bd20f311382716f1/Assigned/Instructions.v#L9-L11) mit den Eigenschaften [`Instructions.Ok x`](../01475aea5b02484677b4a155bd20f311382716f1/Assigned/Instructions.v#L62-L71) und [`Instructions.Closed x`](../01475aea5b02484677b4a155bd20f311382716f1/Assigned/Instructions.v#L73-L77) darstellen.
Für einen Spieler `p` repräsentiert das Tupel `(Up, p)` und `(Down, p)` die Position seiner ersten bzw. letzten Karte im zu mischenden Kartenstapel.

Eine reguläre [Färbung](../5e069a83451f5fb90b11660d0e3c04a0cd9825e2/Coloring.v#L11-L16) muss [dicht](../5e069a83451f5fb90b11660d0e3c04a0cd9825e2/Coloring.v#L54-L59) und für alle [Suffixe](../5e069a83451f5fb90b11660d0e3c04a0cd9825e2/List.v#L168-L170) von `x` [gültig](../5e069a83451f5fb90b11660d0e3c04a0cd9825e2/Assigned/Dyer.v#L1229-L1238) sein.
Zudem sollte die Anzahl der verwendeten Farben mit der [chromatischen Zahl](../5e069a83451f5fb90b11660d0e3c04a0cd9825e2/Assigned/Instructions.v#L623-L632) des zugrundeliegenden Intervallgraphen übereinstimmen.
Der Beweis der Korrektheit des [Algorithmus](../5e069a83451f5fb90b11660d0e3c04a0cd9825e2/Assigned/Dyer.v#L117-L148) für reguläre Färbungen ist [hier](../5e069a83451f5fb90b11660d0e3c04a0cd9825e2/Assigned/Dyer.v#L1324-L1359) einsehbar.

Mit [`counter`](../f0654a32f6812f38780a46c8ef060b6aea72edd2/Assigned/Dyer.v#L763-L766) berechnen wir effizient die chromatische Zahl des Intervallgraphen.
Das Lemma [`counter_spec`](../f0654a32f6812f38780a46c8ef060b6aea72edd2/Assigned/Dyer.v#L1001-L1041) beinhaltet die Spezifikation und Verifikation von `counter`.
