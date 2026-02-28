/**
 * GoAI — simple heuristic Go AI that runs in the browser.
 *
 * Exposes a single function:
 *   window.GoAI.getBestMove(board, aiColor, boardSize, previousBoard)
 *
 * Returns { row, col } for the chosen move, or null if the AI should pass.
 *
 * Priority order:
 *   1. Capture any opponent group that has exactly 1 liberty (atari)
 *   2. Save any of the AI's own groups that are in atari
 *   3. Play adjacent to an existing stone, but only in contested/useful areas
 *   4. Any legal move that is NOT inside clearly settled opponent territory
 *   5. Pass (return null) — all remaining moves would be pointless
 *
 * Territory filter: empty regions that are completely enclosed by one color are
 * labelled as that color's territory. The AI will not voluntarily play inside
 * clearly settled opponent territory, and will pass once no useful moves remain.
 */
window.GoAI = (function () {

  var EMPTY = null;
  var BLACK = 'black';
  var WHITE = 'white';

  function opponent(color) {
    return color === BLACK ? WHITE : BLACK;
  }

  function copyBoard(board) {
    return board.map(function (row) { return row.slice(); });
  }

  function neighbors(row, col, size) {
    var list = [];
    if (row > 0)        list.push([row - 1, col]);
    if (row < size - 1) list.push([row + 1, col]);
    if (col > 0)        list.push([row, col - 1]);
    if (col < size - 1) list.push([row, col + 1]);
    return list;
  }

  // Flood-fill to find all connected stones of `color` starting at (row, col).
  function getGroup(board, row, col, color, size, visited) {
    visited = visited || new Set();
    var key = row + ',' + col;
    if (visited.has(key)) return [];
    if (row < 0 || row >= size || col < 0 || col >= size) return [];
    if (board[row][col] !== color) return [];

    visited.add(key);
    var group = [{ row: row, col: col }];

    var nbrs = neighbors(row, col, size);
    for (var i = 0; i < nbrs.length; i++) {
      var sub = getGroup(board, nbrs[i][0], nbrs[i][1], color, size, visited);
      for (var j = 0; j < sub.length; j++) group.push(sub[j]);
    }
    return group;
  }

  // Count the number of unique empty intersections adjacent to a group.
  function countLiberties(board, group, size) {
    var libs = new Set();
    for (var i = 0; i < group.length; i++) {
      var nbrs = neighbors(group[i].row, group[i].col, size);
      for (var j = 0; j < nbrs.length; j++) {
        var r = nbrs[j][0], c = nbrs[j][1];
        if (board[r][c] === EMPTY) libs.add(r + ',' + c);
      }
    }
    return libs.size;
  }

  // Get the set of liberty coordinates for a group.
  function getLibertySet(board, group, size) {
    var libs = new Set();
    for (var i = 0; i < group.length; i++) {
      var nbrs = neighbors(group[i].row, group[i].col, size);
      for (var j = 0; j < nbrs.length; j++) {
        var r = nbrs[j][0], c = nbrs[j][1];
        if (board[r][c] === EMPTY) libs.add(r + ',' + c);
      }
    }
    return libs;
  }

  function boardsEqual(b1, b2, size) {
    if (!b1 || !b2) return false;
    for (var i = 0; i < size; i++) {
      for (var j = 0; j < size; j++) {
        if (b1[i][j] !== b2[i][j]) return false;
      }
    }
    return true;
  }

  /**
   * Simulate placing `color` at (row, col).
   * Returns { newBoard, captured } if legal, or null if the move is illegal.
   */
  function tryPlace(board, row, col, color, size) {
    if (board[row][col] !== EMPTY) return null;

    var newBoard = copyBoard(board);
    newBoard[row][col] = color;
    var opp = opponent(color);
    var captured = 0;
    var checkedGroups = new Set();

    var nbrs = neighbors(row, col, size);
    for (var i = 0; i < nbrs.length; i++) {
      var nr = nbrs[i][0], nc = nbrs[i][1];
      if (newBoard[nr][nc] === opp) {
        var key = nr + ',' + nc;
        if (!checkedGroups.has(key)) {
          var group = getGroup(newBoard, nr, nc, opp, size);
          for (var g = 0; g < group.length; g++) {
            checkedGroups.add(group[g].row + ',' + group[g].col);
          }
          if (countLiberties(newBoard, group, size) === 0) {
            for (var g2 = 0; g2 < group.length; g2++) {
              newBoard[group[g2].row][group[g2].col] = EMPTY;
              captured++;
            }
          }
        }
      }
    }

    // Suicide check
    var ownGroup = getGroup(newBoard, row, col, color, size);
    if (countLiberties(newBoard, ownGroup, size) === 0 && captured === 0) {
      return null;
    }

    return { newBoard: newBoard, captured: captured };
  }

  function isLegal(board, row, col, color, size, previousBoard) {
    var result = tryPlace(board, row, col, color, size);
    if (!result) return false;
    if (boardsEqual(result.newBoard, previousBoard, size)) return false;
    return true;
  }

  // Shuffle an array in place and return it (Fisher-Yates).
  function shuffle(arr) {
    for (var i = arr.length - 1; i > 0; i--) {
      var j = Math.floor(Math.random() * (i + 1));
      var tmp = arr[i]; arr[i] = arr[j]; arr[j] = tmp;
    }
    return arr;
  }

  function pickRandom(arr) {
    return arr[Math.floor(Math.random() * arr.length)];
  }

  // ---------------------------------------------------------------------------
  // Territory map
  // ---------------------------------------------------------------------------

  /**
   * Flood-fill every empty region on the board and label it by who owns it.
   *
   * An empty region is "owned" by a color when ALL of these are true:
   *   1. Every stone bordering it belongs to that same color.
   *   2. The region is small enough to be a genuine enclosure (not a huge open area).
   *   3. Enough stones are already on the board to make territory judgements meaningful.
   *
   * Returns a plain object mapping "row,col" → 'black' | 'white'.
   * Only settled intersections appear as keys; everything else is absent (contested/open).
   */
  function buildTerritoryMap(board, size) {
    var ownerMap = {};

    // Count stones. If the board is nearly empty it is too early to judge territory —
    // a single stone would otherwise label the whole board as its color's territory.
    var totalStones = 0;
    for (var i = 0; i < size; i++) {
      for (var j = 0; j < size; j++) {
        if (board[i][j] !== EMPTY) totalStones++;
      }
    }
    if (totalStones < size) return ownerMap; // opening — no filtering yet

    // Regions larger than this are open/contested regardless of who borders them.
    // This stops a single stone from "claiming" 80 empty cells on a fresh board.
    var maxSettledRegion = Math.floor(size * size / 4);

    var visited = new Set();

    for (var startR = 0; startR < size; startR++) {
      for (var startC = 0; startC < size; startC++) {
        var startKey = startR + ',' + startC;
        if (visited.has(startKey)) continue;
        if (board[startR][startC] !== EMPTY) continue;

        // BFS over this empty region
        var region = [];
        var borderingColors = new Set();
        var stack = [[startR, startC]];
        var localVisited = new Set();

        while (stack.length > 0) {
          var curr = stack.pop();
          var cr = curr[0], cc = curr[1];
          var cKey = cr + ',' + cc;

          if (localVisited.has(cKey)) continue;
          if (cr < 0 || cr >= size || cc < 0 || cc >= size) continue;

          var cell = board[cr][cc];
          if (cell !== EMPTY) {
            borderingColors.add(cell);
            continue;
          }

          localVisited.add(cKey);
          region.push(cKey);

          var nbrs = neighbors(cr, cc, size);
          for (var k = 0; k < nbrs.length; k++) {
            stack.push(nbrs[k]);
          }
        }

        localVisited.forEach(function (k) { visited.add(k); });

        // Only mark as settled territory if:
        //   - exactly one color borders this region, AND
        //   - the region is small enough to be a real enclosure
        if (borderingColors.size === 1 && region.length <= maxSettledRegion) {
          var iter = borderingColors.values();
          var owner = iter.next().value;
          for (var ri = 0; ri < region.length; ri++) {
            ownerMap[region[ri]] = owner;
          }
        }
        // Large or contested regions are left out of the map entirely.
        // Absent keys read as undefined, so the "=== opp" filter never blocks them.
      }
    }

    return ownerMap;
  }

  // ---------------------------------------------------------------------------
  // Move finders
  // ---------------------------------------------------------------------------

  /**
   * Find empty intersections that capture at least one opponent group in atari.
   * An opponent group is in atari when it has exactly 1 liberty — playing there captures it.
   */
  function findCaptureMoves(board, color, size, previousBoard) {
    var opp = opponent(color);
    var moves = [];
    var checkedGroups = new Set();

    for (var r = 0; r < size; r++) {
      for (var c = 0; c < size; c++) {
        if (board[r][c] === opp) {
          var key = r + ',' + c;
          if (checkedGroups.has(key)) continue;
          var group = getGroup(board, r, c, opp, size);
          for (var g = 0; g < group.length; g++) {
            checkedGroups.add(group[g].row + ',' + group[g].col);
          }
          if (countLiberties(board, group, size) === 1) {
            var libs = getLibertySet(board, group, size);
            libs.forEach(function (lib) {
              var parts = lib.split(',');
              var lr = parseInt(parts[0]), lc = parseInt(parts[1]);
              if (isLegal(board, lr, lc, color, size, previousBoard)) {
                moves.push({ row: lr, col: lc });
              }
            });
          }
        }
      }
    }
    return moves;
  }

  /**
   * Find moves that save the AI's own groups that are in atari.
   * For each group in atari, the single remaining liberty is the escape point.
   */
  function findEscapeMoves(board, color, size, previousBoard) {
    var moves = [];
    var checkedGroups = new Set();

    for (var r = 0; r < size; r++) {
      for (var c = 0; c < size; c++) {
        if (board[r][c] === color) {
          var key = r + ',' + c;
          if (checkedGroups.has(key)) continue;
          var group = getGroup(board, r, c, color, size);
          for (var g = 0; g < group.length; g++) {
            checkedGroups.add(group[g].row + ',' + group[g].col);
          }
          if (countLiberties(board, group, size) === 1) {
            var libs = getLibertySet(board, group, size);
            libs.forEach(function (lib) {
              var parts = lib.split(',');
              var lr = parseInt(parts[0]), lc = parseInt(parts[1]);
              if (isLegal(board, lr, lc, color, size, previousBoard)) {
                moves.push({ row: lr, col: lc });
              }
            });
          }
        }
      }
    }
    return moves;
  }

  /**
   * Find empty intersections adjacent to any existing stone on the board,
   * excluding intersections that are clearly inside any settled territory
   * (both opponent territory and the AI's own settled territory are pointless to fill).
   */
  function findExpansionMoves(board, color, size, previousBoard, territoryMap) {
    var opp = opponent(color);
    var moves = [];
    var seen = new Set();

    for (var r = 0; r < size; r++) {
      for (var c = 0; c < size; c++) {
        if (board[r][c] !== EMPTY) {
          var nbrs = neighbors(r, c, size);
          for (var i = 0; i < nbrs.length; i++) {
            var nr = nbrs[i][0], nc = nbrs[i][1];
            var key = nr + ',' + nc;
            if (!seen.has(key) && board[nr][nc] === EMPTY) {
              seen.add(key);
              // Skip intersections inside any settled territory — both opponent
              // territory (losing) and own territory (reduces own score)
              if (territoryMap[key] === opp) continue;
              if (territoryMap[key] === color) continue;
              if (isLegal(board, nr, nc, color, size, previousBoard)) {
                moves.push({ row: nr, col: nc });
              }
            }
          }
        }
      }
    }
    return moves;
  }

  /**
   * Build the list of all legal moves outside any clearly settled territory.
   * Used as the last-resort fallback before passing.
   */
  function findUsefulLegalMoves(board, color, size, previousBoard, territoryMap) {
    var opp = opponent(color);
    var moves = [];
    for (var r = 0; r < size; r++) {
      for (var c = 0; c < size; c++) {
        var key = r + ',' + c;
        if (board[r][c] !== EMPTY) continue;
        if (territoryMap[key] === opp) continue;    // inside opponent territory
        if (territoryMap[key] === color) continue;  // inside own territory
        if (isLegal(board, r, c, color, size, previousBoard)) {
          moves.push({ row: r, col: c });
        }
      }
    }
    return moves;
  }

  // ---------------------------------------------------------------------------
  // Main entry point
  // ---------------------------------------------------------------------------

  /**
   * Choose the best move for the AI.
   *
   * @param {Array}  board         - 2D array, null = empty, 'black'/'white' = stone
   * @param {string} aiColor       - 'black' or 'white'
   * @param {number} boardSize     - 9 or 13
   * @param {Array}  previousBoard - board state before the last move (for Ko), may be null
   * @returns {{ row: number, col: number } | null}  null means the AI passes
   */
  function getBestMove(board, aiColor, boardSize, previousBoard) {

    // Priority 1 — capture opponent groups in atari (always worthwhile)
    var captures = shuffle(findCaptureMoves(board, aiColor, boardSize, previousBoard));
    if (captures.length > 0) return pickRandom(captures);

    // Priority 2 — save own groups in atari (always worthwhile)
    var escapes = shuffle(findEscapeMoves(board, aiColor, boardSize, previousBoard));
    if (escapes.length > 0) return pickRandom(escapes);

    // Build the territory map once — used by all remaining priorities
    var tMap = buildTerritoryMap(board, boardSize);

    // Priority 3 — expand near existing stones, but only in useful areas
    var expansions = shuffle(findExpansionMoves(board, aiColor, boardSize, previousBoard, tMap));
    if (expansions.length > 0) return pickRandom(expansions);

    // Priority 4 — any legal move outside settled opponent territory
    var useful = shuffle(findUsefulLegalMoves(board, aiColor, boardSize, previousBoard, tMap));
    if (useful.length > 0) return pickRandom(useful);

    // Nothing useful to do — pass
    return null;
  }

  return { getBestMove: getBestMove };

})();
