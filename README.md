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

Der Beweis der Korrektheit des Algorithmus für gültige Färbungen ist [hier](../main/Assigned/Dyer.v#L532) einsehbar.
