# Cached Diagonal U Patterns

`U` marks non-full vertices and `.` marks full vertices. These are cached from
`fullub-pattern n n` runs so pattern analysis does not need to rerun the
expensive witness DP.

## n = 12

```text
..........U.
UUUUUUUUUUU.
UU.UUUUUUUU.
.UUU......U.
.UUUUUUUUUU.
.U..UUUUUUU.
.UUUU.....U.
.UUUUUUUUUU.
.U...UUU.UU.
.UUUUU.UUUU.
.UUUUUUUUUUU
.U..........
```

## n = 13

```text
.U...........
.UUUUUUUUUUUU
.UUUUUUUUUUUU
.U...........
.UUUUUUUUUUUU
.UUUUUUUUUUUU
.U...........
.UUUUUUUUUUUU
.UUUUUUUUUUUU
.U...........
.UUUUUUUUUUUU
UUUUUUUUUUUUU
.............
```

## n = 14

```text
.U............
.UUUUUUUUUUUUU
.UUUU.UU.UU.UU
.UU.UUUU.UUUU.
.UU.UU.UUU.UU.
.UU.UU.UUU.UU.
.UU.UU.U.U.UU.
.UU.UU.UUU.UU.
.UU.UU.UUU.UU.
.UU.UU.U.UUUU.
.UU.UU.UUUU.U.
.UU.UU.UU.UUU.
.UUUUUUUUUUUU.
.U..........U.
```

## n = 15

```text
.............U.
UUUUUUUUUUUUUU.
.UU.UUUUUUUUUU.
.UU.UU.......U.
.UU.UUUUUUUUUU.
.UU.U.UU.UU.UU.
.UUUU.UU.UU.UU.
.U.UU.UU.UU.UU.
.UUUU.UU.UU.UU.
.UU.UUUU.UU.UU.
.UU.UU.UUUU.UU.
.UU.UU.UU.UUUU.
.UU.UU.UU.UU.U.
.UUUUUUUUUUUUU.
.U..........UU.
```
