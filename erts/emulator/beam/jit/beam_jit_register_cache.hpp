/*
 * %CopyrightBegin%
 *
 * Copyright Ericsson AB 2024. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * %CopyrightEnd%
 */

#ifndef __BEAM_JIT_REGISTER_CACHE_HPP__
#define __BEAM_JIT_REGISTER_CACHE_HPP__

#include <functional>
#include <algorithm>
#include <limits>

template<int Size, typename Mem, typename Reg>
class RegisterCache {
    struct CacheEntry {
        Mem mem;
        Reg reg;
    };

    CacheEntry cache[Size];
    int entries;
    size_t position;
    const std::vector<Reg> temporaries;

    CacheEntry *begin() {
        return std::begin(cache);
    }

    CacheEntry *end() {
        return begin() + entries;
    }

    bool isCached(const Reg &reg) {
        return std::any_of(begin(), end(), [&](const auto &entry) {
            return (reg == entry.reg) ||
                   (entry.mem.hasBase() && entry.mem.baseReg() == reg);
        });
    }

public:
    RegisterCache(std::initializer_list<Reg> &&tmps)
            : entries(0), position(std::numeric_limits<size_t>::max()),
              temporaries(tmps) {
    }

    void consolidate(size_t offset) {
        if (!validAt(offset)) {
            invalidate();
        }

        position = offset;
    }

    Reg find(size_t offset, Mem mem) {
        ASSERT(mem.hasBase());
        consolidate(offset);

        auto it = std::find_if(begin(), end(), [&](const auto &entry) {
            return mem == entry.mem;
        });

        if (it != end()) {
            ASSERT(it->reg.isValid() && isCached(it->reg));
            return it->reg;
        }

        return Reg();
    }

    void invalidate(Mem mem) {
        ASSERT(mem.hasBase());

        auto i = 0;
        while (i < entries) {
            auto &entry = cache[i];

            if (entry.mem == mem) {
                entry = cache[entries - 1];
                entries--;
                continue;
            }

            i++;
        }
    }

    void invalidate(Reg reg) {
        ASSERT(reg.isValid());

        auto i = 0;
        while (i < entries) {
            auto &entry = cache[i];

            if (reg == entry.reg || entry.mem.baseReg() == reg) {
                entry = cache[entries - 1];
                entries--;
                continue;
            }

            i++;
        }
    }

    void invalidate() {
        position = std::numeric_limits<size_t>::max();
        entries = 0;
    }

    template<typename Operand, typename... Operands>
    void invalidate(Operand op, Operands... rest) {
        invalidate(op);
        invalidate(rest...);
    }

    /* Picks a temporary register among the list passed to our constructor,
     * preferring those not present in the cache. */
    Reg allocate(size_t offset) {
        consolidate(offset);

        auto it = std::find_if(temporaries.cbegin(),
                               temporaries.cend(),
                               [&](const auto &reg) {
                                   return !isCached(reg);
                               });

        if (it != temporaries.cend()) {
            return *it;
        }

        return temporaries.front();
    }

    void put(Mem mem, Reg reg) {
        ASSERT(mem.hasBase());

        if (mem.baseReg() != reg) {
            auto it = std::find_if(begin(), end(), [&](const auto &entry) {
                return mem == entry.mem;
            });

            if (it == end()) {
                if (it == std::end(cache)) {
                    ASSERT(entries == Size);
                    it = std::begin(cache);
                } else {
                    ASSERT(entries < Size);
                    entries++;
                }
            }

            it->reg = reg;
            it->mem = mem;
        }
    }

    void update(size_t offset) {
        position = offset;
    }

    bool validAt(size_t offset) {
        return position == offset;
    }
};

#endif
