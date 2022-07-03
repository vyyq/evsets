#include "algorithms.h"
#include "list_utils.h"
#include "public_structs.h"
#include "utils.h"
#include <math.h>
#include <stdio.h>

#define MAX_REPS_BACK 1000000

extern struct config conf;

int naive_eviction(Elem **ptr, Elem **can, char *victim) {
  Elem *candidate = NULL;
  int len = 0, cans = 0, i = 0, fail = 0, ret = 0, repeat = 0;

  len = list_length(*ptr);
  cans = list_length(*can);

  while (len > conf.cache_way) {
    if (conf.ratio > 0.0) {
      ret = tests(*ptr, victim, conf.rounds, conf.threshold, conf.ratio,
                  conf.traverse);
    } else {
      ret = tests_avg(*ptr, victim, conf.rounds, conf.threshold, conf.traverse);
    }
    if (ret) {
      candidate = list_pop(ptr);
      list_push(can, candidate);
      fail = 0;
    } else if (!cans) {
      break;
    } else {
      // candidate is part of the eviction set, put it back at the end
      candidate = list_pop(can);
      list_append(ptr, candidate);
      if (fail) {
        // step back in decision binary tree by readding previous candidate
        if (!(conf.flags & FLAG_BACKTRACKING) || repeat > MAX_REPS_BACK) {
          break;
        }
        repeat++;
        if (conf.flags & FLAG_VERBOSE) {
          printf("\tbacktrack one step\n");
        }
      }
      fail = 1;
    }

    len = list_length(*ptr);
    cans = list_length(*can);

    if ((conf.flags & FLAG_VERBOSE) && !(i++ % 300)) {
      printf("\teset=%d, removed=%d (%d)\n", len, cans, len + cans);
    }
  }

  if (conf.flags & FLAG_VERBOSE) {
    printf("\teset=%d, removed=%d (%d)\n", len, cans, len + cans);
  }

  if (conf.ratio > 0.0) {
    ret = tests(*ptr, victim, conf.rounds, conf.threshold, conf.ratio,
                conf.traverse);
  } else {
    ret = tests_avg(*ptr, victim, conf.rounds, conf.threshold, conf.traverse);
  }
  if (ret) {
    // Not fully reduced (exceed backtrack steps)
    if (len > conf.cache_way) {
      return 1;
    }
  } else {
    return 1;
  }
  return 0;
}

int naive_eviction_optimistic(Elem **ptr, Elem **can, char *victim) {
  Elem *candidate = NULL, *es = NULL;
  int len = 0, cans = 0, elen = 0, i = 0, ret = 0;

  len = list_length(*ptr);

  while (elen < conf.cache_way && len > conf.cache_way) {
    candidate = list_pop(ptr);

    if (conf.ratio > 0.0) {
      ret = tests(*ptr, victim, conf.rounds, conf.threshold, conf.ratio,
                  conf.traverse);
    } else {
      ret = tests_avg(*ptr, victim, conf.rounds, conf.threshold, conf.traverse);
    }
    if (ret) {
      // list still is an eviction set of victim
      // discard candidate
      list_push(can, candidate);
    } else {
      // candidate is congruent, keep it
      elen++;
      if (!es) {
        // pointer to eviction set sublist
        es = candidate;
      }
      list_append(ptr, candidate);
    }

    len = list_length(*ptr);
    cans = list_length(*can);

    if ((conf.flags & FLAG_VERBOSE) && !(i++ % 300)) {
      printf("\teset=%d, removed=%d (%d)\n", len, cans, len + cans);
    }
  }

  if (conf.flags & FLAG_VERBOSE) {
    printf("\teset=%d, removed=%d (%d)\n", len, cans, len + cans);
  }

  list_concat(can, *ptr);

  if (elen < conf.cache_way) {
    *ptr = NULL;
    return 1;
  } else {
    es->prev->next = NULL;
    es->prev = NULL;
    *ptr = es;
  }

  if (conf.ratio > 0.0) {
    ret = tests(*ptr, victim, conf.rounds, conf.threshold, conf.ratio,
                conf.traverse);
  } else {
    ret = tests_avg(*ptr, victim, conf.rounds, conf.threshold, conf.traverse);
  }
  return !ret;
}

int gt_eviction(Elem **ptr, Elem **can, char *victim) {
  // Random chunk selection
  Elem **chunks = (Elem **)calloc(conf.cache_way + 1, sizeof(Elem *));
  if (!chunks) {
    return 1;
  }
  int *chunk_idxs = (int *)calloc(conf.cache_way + 1, sizeof(int));
  int i;
  if (!chunk_idxs) {
    free(chunks);
    return 1;
  }

  // The size of the current eviction set
  int evset_size = list_length(*ptr);
  int nr_removed_lines = 0;

  double sz = (double)conf.cache_way / evset_size;
  double rate = (double)conf.cache_way / (conf.cache_way + 1);
  int h = ceil(log(sz) / log(rate)); // h = log(a/(a+1), a/n)
  int level = 0;                     // Nr of iterations of reduction

  // Backtrack record
  Elem **backtrack_record =
      (Elem **)calloc(h * 2, sizeof(Elem *)); // TODO: check height bound
  if (backtrack_record == NULL) {
    free(chunks);
    free(chunk_idxs);
    return 1;
  }

  int repeat = 0; // # backtracking which has already been done.
  int retest_res;

  do {
    // Assign an index array and shuffle it
    for (i = 0; i < conf.cache_way + 1; i++) {
      chunk_idxs[i] = i;
    }
    shuffle(chunk_idxs, conf.cache_way + 1);

    // Reduce
    while (evset_size > conf.cache_way) {
      list_split(*ptr, chunks, conf.cache_way + 1);

      // The index of the chunk which is being tested now
      int n = 0;
      // bool: if the subset can evict the victim
      int sublist_can_evict_victim = 0;

      do {
        list_from_chunks(ptr, chunks, chunk_idxs[n], conf.cache_way + 1);
        n++;
        if (conf.ratio > 0.0) {
          sublist_can_evict_victim =
              tests(*ptr, victim, conf.rounds, conf.threshold, conf.ratio,
                    conf.traverse);
        } else {
          sublist_can_evict_victim = tests_avg(*ptr, victim, conf.rounds,
                                               conf.threshold, conf.traverse);
        }
      } while (sublist_can_evict_victim == 0 && (n < conf.cache_way + 1));

      // If a smaller eviction set is found, remove the chunk
      if (sublist_can_evict_victim && n <= conf.cache_way) {
        backtrack_record[level] = chunks[chunk_idxs[n - 1]];
        nr_removed_lines += list_length(backtrack_record[level]);
        evset_size = list_length(*ptr);

        if (conf.flags & FLAG_VERBOSE) {
          printf("\t" SUCCESS_STATUS_PREFIX
                 "Successful reduction iteration: level = %d: evset size = %d, "
                 "removed lines = "
                 "%d, total lines = %d\n",
                 level, evset_size, nr_removed_lines,
                 evset_size + nr_removed_lines);
        }
        level++; // go to the next lvl
      } else if (level > 0) { // If not, recover to the last iteration
        list_concat(ptr, chunks[chunk_idxs[n - 1]]);
        level--;
        nr_removed_lines -= list_length(backtrack_record[level]);
        list_concat(ptr, backtrack_record[level]);
        backtrack_record[level] = NULL;
        evset_size = list_length(*ptr);
        goto continue_backtracking;
      } else {
        list_concat(ptr, chunks[chunk_idxs[n - 1]]); // recover
        goto stop_reduction;
      }
    } // while (evset_size > conf.cache_way)

    goto stop_reduction;

  continue_backtracking:
    printf(FAILURE_STATUS_PREFIX "Reduction failed. Retesting original set...\n");
    retest_res =
        tests_avg(*ptr, victim, conf.rounds, conf.threshold, conf.traverse);

    if (conf.flags & FLAG_VERBOSE) {
      if (retest_res == 0)
        printf(FAILURE_STATUS_PREFIX
               "The original larger set is not actually an eviction set\n");
      else
        printf(
            "\t" FAILURE_STATUS_PREFIX
            "Reduction failed. Backtracking towards level %d... (Backtracking "
            "has already be "
            "performed %d times; max toleration = %d)\n",
            level, repeat, MAX_REPS_BACK);
    }
    if (retest_res == 0)
      goto stop_reduction;
    else
      continue;
  } while (level > 0 && repeat++ < MAX_REPS_BACK &&
           (conf.flags & FLAG_BACKTRACKING));

stop_reduction:
  // recover discarded elements
  for (i = 0; i < h * 2; i++) {
    list_concat(can, backtrack_record[i]);
  }

  free(chunks);
  free(chunk_idxs);
  free(backtrack_record);

  int ret = 0;
  if (conf.ratio > 0.0) {
    ret = tests(*ptr, victim, conf.rounds, conf.threshold, conf.ratio,
                conf.traverse);
  } else {
    ret = tests_avg(*ptr, victim, conf.rounds, conf.threshold, conf.traverse);
  }
  if (ret) {
    if (evset_size > conf.cache_way) {
      return 1;
    }
  } else {
    return 1;
  }

  return 0;
}

int gt_eviction_any(Elem **ptr, Elem **can) {
  Elem **chunks = (Elem **)calloc(conf.cache_way + 2, sizeof(Elem *));
  if (!chunks) {
    return 1;
  }
  // Random chunk selection
  int *ichunks = (int *)calloc(conf.cache_way + 2, sizeof(int)), i;
  if (!ichunks) {
    free(chunks);
    return 1;
  }

  int len = list_length(*ptr), cans = 0;

  // Calculate length: h = log(a/(a+1), a/n)
  double sz = (double)(conf.cache_way + 1) / len;
  double rate = (double)(conf.cache_way + 1) / (conf.cache_way + 2);
  int h = ceil(log(sz) / log(rate)), l = 0;

  // Backtrack record
  Elem **back = calloc(h * 2, sizeof(Elem *)); // TODO: check height bound
  if (!back) {
    free(chunks);
    free(ichunks);
    return 1;
  }

  int repeat = 0;
  do {
    for (i = 0; i < conf.cache_way + 2; i++) {
      ichunks[i] = i;
    }
    shuffle(ichunks, conf.cache_way + 2);

    while (len > conf.cache_way + 1) {

      list_split(*ptr, chunks, conf.cache_way + 2);
      int n = 0, ret = 0;

      do {
        list_from_chunks(ptr, chunks, ichunks[n], conf.cache_way + 2);
        n = n + 1;
      } while (!(ret = (test_and_time(*ptr, conf.rounds, conf.threshold,
                                      conf.cache_way, conf.traverse))) &&
               (n < conf.cache_way + 2));

      // If find smaller eviction set remove chunk
      if (ret && n <= conf.cache_way + 1) {
        back[l] = chunks[ichunks[n - 1]]; // store ptr to discarded chunk
        cans += list_length(back[l]);     // add length of removed chunk
        len = list_length(*ptr);

        if (conf.flags & FLAG_VERBOSE) {
          printf(
              "\tLevel (iteration) = %d: evset size = %d, # removed lines = %d "
              "(%d)\n",
              l, len, cans, len + cans);
        }

        l = l + 1; // go to next lvl
      }
      // Else, re-add last removed chunk and try again
      else if (l > 0) {
        list_concat(ptr, chunks[ichunks[n - 1]]); // recover last case
        l = l - 1;
        cans -= list_length(back[l]);
        list_concat(ptr, back[l]);
        back[l] = NULL;
        len = list_length(*ptr);
        goto mycont;
      } else {
        break;
      }
    }

    break;
  mycont:
    if (conf.flags & FLAG_VERBOSE) {
      printf("\tbacktracking step\n");
    }

  } while (l > 0 && repeat++ < MAX_REPS_BACK &&
           (conf.flags & FLAG_BACKTRACKING));

  // recover discarded elements
  for (i = 0; i < h * 2; i++) {
    list_concat(can, back[i]);
  }

  free(chunks);
  free(ichunks);
  free(back);

  if (test_and_time(*ptr, conf.rounds, conf.threshold, conf.cache_way,
                    conf.traverse)) {
    if (len > conf.cache_way + 1) {
      return 1;
    }
  } else {
    return 1;
  }

  return 0;
}

int binary_eviction(Elem **ptr, Elem **can, char *victim) {
  // shameful inneficient implementation with lists...
  // any good way to add backtracking?
  int olen = list_length(*ptr), len, cans, count = 0, i = 0, ret = 0;
  double x = 0, pivot = 0, laste = 0, lastn = 0;
  Elem *positive = NULL;
  while (count < conf.cache_way) {
    x = 1;
    laste = (double)olen;
    lastn = 0;
    pivot = 0;
    i = 1;
    while (fabs(lastn - laste) > 1 && x < olen) {
      i = i << 1;
      pivot = ceil(x * (olen - conf.cache_way + 1) / i);
      *can = list_slice(ptr, conf.cache_way - 2 + (unsigned int)pivot + 1,
                        olen - 1);
      len = list_length(*ptr);
      cans = list_length(*can);
      if (conf.ratio > 0.0) {
        ret = tests(*ptr, victim, conf.rounds, conf.threshold, conf.ratio,
                    conf.traverse);
      } else {
        ret =
            tests_avg(*ptr, victim, conf.rounds, conf.threshold, conf.traverse);
      }
      if (ret) {
        laste = pivot;
        x = 2 * x - 1;
      } else {
        lastn = pivot;
        x = 2 * x + 1;
      }
      if (conf.flags & FLAG_VERBOSE) {
        printf("\telem==%d eset=%d res=%d (%d)\n", count, len, cans,
               len + cans);
      }
      list_concat(ptr, *can);
      *can = NULL;
    }
    if (pivot + conf.cache_way > olen) {
      printf("[-] Something wrong, quitting\n");
      return 1;
    }
    positive = list_get(ptr, conf.cache_way - 2 + (unsigned int)laste);
    list_push(ptr,
              positive); // re-arrange list for next round (element to head)
    count = count + 1;
  }
  *can = list_slice(ptr, conf.cache_way, len + cans - 1);
  if (conf.ratio > 0.0) {
    ret = tests(*ptr, victim, conf.rounds, conf.threshold, conf.ratio,
                conf.traverse);
  } else {
    ret = tests_avg(*ptr, victim, conf.rounds, conf.threshold, conf.traverse);
  }
  return !ret;
}
