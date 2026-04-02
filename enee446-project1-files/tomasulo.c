/*
 *
 * tomasulo.c  –  corrected implementation
 *
 * Bugs fixed (cumulative list):
 *
 *  [from prior revision]
 *  1. HALT dispatch fell through switch to `default: return`.
 *  2. Branch dispatch never set fetch_lock = TRUE.
 *  3. Structural-hazard stall (fu_lock/fetch_lock) only on branch path.
 *  4. LOAD write-back was an empty comment placeholder.
 *  5. JAL/JALR return address used state->pc+4 (off by 4).
 *  6. JR/JALR returned 1 instead of the actual register value.
 *  7. J/JAL used FIELD_IMM (16-bit) instead of FIELD_OFFSET (26-bit).
 *  8. Float stores (S.S) always used integer.w for store data.
 *  9. reg_map clear didn't guard against overwriting a newer mapping.
 * 10. insn_num now stores the byte-address of the instruction.
 *
 *  [fixed in this revision]
 * 11. Integer-R0 "hardwired zero" convention was incorrectly applied to
 *     floating-point register F0.  In dispatch, `if (r1 != 0)` and
 *     `if (r2 != 0)` skipped the register-file lookup for r==0 even for
 *     DATA_TYPE_F.  This meant MULT.S F0 F0 F0 got fu_1=NULL/fu_2=NULL
 *     (no dependency on the in-flight L.S F0), executed immediately with
 *     0.0×0.0, and the reg_map[0] was never updated.  Fix: skip the
 *     lookup ONLY for integer register 0.
 *
 * 12. clear_map_fp used `reg > 0` (same wrong guard), so F0's mapping
 *     could never be cleared after broadcast.  Fix: use `reg >= 0`.
 *
 * 13. Branch / jump targets were computed as  orig_pc + offset  instead of
 *     the correct  orig_pc + 4 + offset.  The assembler encodes
 *       offset = target – (PC + 4)
 *     so the simulator must add 4 back.  Without this fix `j loop` jumped
 *     one instruction early, causing an infinite loop.
 */
 
#include <stdlib.h>
#include <string.h>
#include "fu.h"
#include "tomasulo.h"

#define MAX_TRACKED_FU 256

static unsigned long issue_seq_counter = 1;
static unsigned long issue_pc[MAX_TRACKED_FU];
static int halt_pending = 0;
 
/* -----------------------------------------------------------------------
 * fetch
 * ----------------------------------------------------------------------- */
void fetch(state_t *state)
{
    if (state->halted || state->fetch_lock) // Dont fetch if halted or locked
        return;
 
    // Parse the instruction from multiple memory locations
    state->if_id.instr = (uint32_t) state->mem[state->pc] | ((uint32_t)state->mem[state->pc + 1] <<  8) | ((uint32_t)state->mem[state->pc + 2] << 16) | ((uint32_t)state->mem[state->pc + 3] << 24);
 
    state->if_id.insn_num = state->pc; // Store the PC
    state->pc += 4; // Increment the PC
}
 
/* -----------------------------------------------------------------------
 * dispatch
 * ----------------------------------------------------------------------- */
 
/* Is this an integer instruction (so register 0 is hardwired zero)?  */
static int is_int_type(const op_info_t *op_info)
{
    return op_info->data_type != DATA_TYPE_F;
}

/* Stall younger non-branch dispatch while any unresolved branch is in ALU RS. */
static int has_pending_branch(fu_t *fu_list)
{
    fu_t *fu = fu_list;
    while (fu != NULL) {
        if (fu->busy) {
            int use_imm;
            const op_info_t *info = decode_instr(fu->instr, &use_imm);
            if (info->fu_group_num == FU_GROUP_BRANCH)
                return TRUE;
        }
        fu = fu->next;
    }
    return FALSE;
}
 
void dispatch(state_t *state)
{
    if (state->halted)
        return;

    if (halt_pending) {
        state->fetch_lock = TRUE;
        return;
    }
 
    if (state->if_id.insn_num == state->pc) {
        return;
    }
    state->fu_lock = FALSE;
 
    int use_imm;
    const op_info_t *op_info = decode_instr((uint32_t)state->if_id.instr, &use_imm);
 
    
    if (op_info->fu_group_num == FU_GROUP_NONE)    return;  /* NOP  */
    if (op_info->fu_group_num == FU_GROUP_INVALID) return;  /* bad  */
 
    /* HALT must not retire ahead of unresolved control-flow instructions. */
    if (op_info->fu_group_num == FU_GROUP_HALT) {
        if (has_pending_branch(state->int_rs_list)) {
            state->fetch_lock = TRUE;
            return;
        }
        halt_pending = 1;
        return;
    }

    fu_t *fu_list = NULL;
    switch (op_info->fu_group_num) {
        case FU_GROUP_INT:    fu_list = state->int_rs_list;     break;
        case FU_GROUP_ADD:    fu_list = state->fp_add_rs_list;  break;
        case FU_GROUP_MULT:   fu_list = state->fp_mult_rs_list; break;
        case FU_GROUP_DIV:    fu_list = state->fp_div_rs_list;  break;
        case FU_GROUP_MEM:    fu_list = state->mem_fu_list;     break;
        case FU_GROUP_BRANCH: fu_list = state->int_rs_list;     break;
        default: return;
    }
 
    if (op_info->fu_group_num != FU_GROUP_BRANCH && has_pending_branch(state->int_rs_list)) {
        state->fetch_lock = TRUE;
        return;
    }

    if (op_info->fu_group_num != FU_GROUP_BRANCH)
        state->fetch_lock = FALSE;

    fu_t *fu = find_available_fu(fu_list);
    if (fu == NULL) {
        state->fu_lock = TRUE;
        return;
    }

    
 
    fu->busy     = TRUE;
    fu->instr    = (uint32_t)state->if_id.instr;
    fu->insn_num = issue_seq_counter++;
    fu->cycles   = fu->max_cycles;
    fu->fu_1     = NULL;
    fu->fu_2     = NULL;

    if (fu->id >= 0 && fu->id < MAX_TRACKED_FU)
        issue_pc[fu->id] = state->if_id.insn_num;

    uint32_t instr = fu->instr;
    int r1  = (int)FIELD_R1(instr);
    int r2  = (int)FIELD_R2(instr);
    int r3  = (int)FIELD_R3(instr);
    int imm = (int)FIELD_IMM(instr);
    int fp  = (op_info->data_type == DATA_TYPE_F);   /* float instruction? */
 
    /* ---- Operand 1 ---------------------------------------------------- */
    /* For MEM instructions (L.S, S.S, LW, SW), the base address register
     * (r1) is ALWAYS an integer register, even for float loads/stores.
     * Only look up float registers for fp arithmetic (ADD, MULT, DIV, SUB).
     * Using reg_map_fp[r1] for a MEM instruction creates a false dependency
     * when a prior fp instruction has mapped that float register number.    */
    int op1_is_fp = fp && (op_info->fu_group_num != FU_GROUP_MEM);
 
    if (r1 != 0 || op1_is_fp) {
        if (op1_is_fp) {
            if (state->reg_map_fp[r1] != NULL)
                fu->fu_1 = state->reg_map_fp[r1];
            else
                fu->operand_1.flt = state->rf_fp.reg_fp[r1];
        } else {
            if (state->reg_map_int[r1] != NULL)
                fu->fu_1 = state->reg_map_int[r1];
            else
                fu->operand_1.integer = state->rf_int.reg_int[r1];
        }
    } else {
        /* integer R0 = 0 */
        fu->operand_1.integer.w = 0;
    }
 
    /* ---- Operand 2 ---------------------------------------------------- */
    if (op_info->fu_group_num == FU_GROUP_MEM) {
 
        if (op_info->operation == OPERATION_LOAD) {
            fu->operand_2.integer.w = imm;          /* byte offset, no hazard */
        } else {
            /* STORE: operand_2 = data register (r2). */
            if (fp) {
                if (r2 != 0 || fp) {                /* F0 is valid source */
                    if (state->reg_map_fp[r2] != NULL)
                        fu->fu_2 = state->reg_map_fp[r2];
                    else
                        fu->operand_2.flt = state->rf_fp.reg_fp[r2];
                } else {
                    fu->operand_2.flt = 0.0f;
                }
            } else {
                if (r2 != 0) {
                    if (state->reg_map_int[r2] != NULL)
                        fu->fu_2 = state->reg_map_int[r2];
                    else
                        fu->operand_2.integer = state->rf_int.reg_int[r2];
                } else {
                    fu->operand_2.integer.w = 0;
                }
            }
        }

    } else if (op_info->fu_group_num == FU_GROUP_BRANCH) {
        fu->operand_2.integer.w = imm;
 
    } else {
        if (use_imm) {
            if (fp)
                fu->operand_2.flt = (float)imm;
            else
                fu->operand_2.integer.w = imm;
        } else {
            /* Same rule: skip lookup only for integer R0. */
            if (r2 != 0 || fp) {
                if (fp) {
                    if (state->reg_map_fp[r2] != NULL)
                        fu->fu_2 = state->reg_map_fp[r2];
                    else
                        fu->operand_2.flt = state->rf_fp.reg_fp[r2];
                } else {
                    if (state->reg_map_int[r2] != NULL)
                        fu->fu_2 = state->reg_map_int[r2];
                    else
                        fu->operand_2.integer = state->rf_int.reg_int[r2];
                }
            } else {
                fu->operand_2.integer.w = 0;
            }
        }
    }
 
    /* ---- Update register map for destination -------------------------- */
    if (op_info->fu_group_num == FU_GROUP_MEM && op_info->operation == OPERATION_LOAD) {
        if (fp)
            state->reg_map_fp[r2] = fu;
        else
            state->reg_map_int[r2] = fu;
 
    } else if (op_info->fu_group_num != FU_GROUP_BRANCH  &&
               op_info->operation   != OPERATION_STORE) {
        int dest = use_imm ? r2 : r3;
        /* Allow dest==0 for float (F0 is a writable register). */
        if (dest != 0 || fp) {
            if (fp)
                state->reg_map_fp[dest] = fu;
            else
                state->reg_map_int[dest] = fu;
        }
    }

    
}
 
/* -----------------------------------------------------------------------
 * execute
 * ----------------------------------------------------------------------- */
void execute(state_t *state)
{
    advance_rs(state->int_rs_list,     &state->cdb_int);
    advance_rs(state->fp_add_rs_list,  &state->cdb_fp);
    advance_rs(state->fp_mult_rs_list, &state->cdb_fp);
    advance_rs(state->fp_div_rs_list,  &state->cdb_fp);
    advance_memory_buffer(state->mem_fu_list, &state->cdb_int, &state->cdb_fp);

    /* Keep stores from counting down while store-data dependency is unresolved. */
    {
        fu_t *mfu = state->mem_fu_list;
        while (mfu != NULL) {
            if (mfu->busy && mfu->fu_1 == NULL && mfu->fu_2 != NULL) {
                int use_imm;
                const op_info_t *info = decode_instr(mfu->instr, &use_imm);
                if (info->operation == OPERATION_STORE)
                    mfu->cycles = mfu->max_cycles;
            }
            mfu = mfu->next;
        }
    }
}
 
/* -----------------------------------------------------------------------
 * broadcast – helpers
 * ----------------------------------------------------------------------- */
 
/* Clear the register-map slot only if it still points at *this* FU.      */
static void clear_map_int(state_t *state, int reg, fu_t *fu)
{
    /* Integer R0 is never in the map. */
    if (reg > 0 && state->reg_map_int[reg] == fu)
        state->reg_map_int[reg] = NULL;
}
static void clear_map_fp(state_t *state, int reg, fu_t *fu)
{
    /* F0 (reg==0) IS a valid mapped register. */
    if (reg >= 0 && state->reg_map_fp[reg] == fu)
        state->reg_map_fp[reg] = NULL;
}
 
static void wake_dependents(state_t *state, fu_t *fu, operand_t result)
{
    update_fu_list(state->int_rs_list,     fu, result);
    update_fu_list(state->fp_add_rs_list,  fu, result);
    update_fu_list(state->fp_mult_rs_list, fu, result);
    update_fu_list(state->fp_div_rs_list,  fu, result);
    update_fu_list(state->mem_fu_list,     fu, result);
}
 
static void release_fu(fu_t *fu)
{
    fu->busy   = FALSE;
    fu->cycles = fu->max_cycles;
}
 
/* -----------------------------------------------------------------------
 * broadcast
 * ----------------------------------------------------------------------- */
void broadcast(state_t *state, int *num_insn)
{
    /* ==================================================================
     * Integer CDB
     * ================================================================== */
    if (state->cdb_int != NULL) {
        fu_t *fu = state->cdb_int;
        state->cdb_int = NULL;
 
        int use_imm;
        const op_info_t *op_info = decode_instr(fu->instr, &use_imm);

        
        uint32_t instr = fu->instr;
 
        operand_t result;
        result.integer.w = 0;
 
        switch (op_info->operation) {
 
            case OPERATION_ADD:
                result.integer.w  = fu->operand_1.integer.w  + fu->operand_2.integer.w;  break;
            case OPERATION_ADDU:
                result.integer.wu = fu->operand_1.integer.wu + fu->operand_2.integer.wu; break;
            case OPERATION_SUB:
                result.integer.w  = fu->operand_1.integer.w  - fu->operand_2.integer.w;  break;
            case OPERATION_SUBU:
                result.integer.wu = fu->operand_1.integer.wu - fu->operand_2.integer.wu; break;
            case OPERATION_SLL:
                result.integer.wu = fu->operand_1.integer.wu << fu->operand_2.integer.w; break;
            case OPERATION_SRL:
                result.integer.wu = fu->operand_1.integer.wu >> fu->operand_2.integer.w; break;
            case OPERATION_AND:
                result.integer.wu = fu->operand_1.integer.wu & fu->operand_2.integer.wu; break;
            case OPERATION_OR:
                result.integer.wu = fu->operand_1.integer.wu | fu->operand_2.integer.wu; break;
            case OPERATION_XOR:
                result.integer.wu = fu->operand_1.integer.wu ^ fu->operand_2.integer.wu; break;
            case OPERATION_SLT:
                result.integer.w  = (fu->operand_1.integer.w  < fu->operand_2.integer.w)  ? 1:0; break;
            case OPERATION_SGT:
                result.integer.w  = (fu->operand_1.integer.w  > fu->operand_2.integer.w)  ? 1:0; break;
            case OPERATION_SLTU:
                result.integer.wu = (fu->operand_1.integer.wu < fu->operand_2.integer.wu) ? 1:0; break;
            case OPERATION_SGTU:
                result.integer.wu = (fu->operand_1.integer.wu > fu->operand_2.integer.wu) ? 1:0; break;
 
            case OPERATION_LOAD: {
                uint32_t addr = (uint32_t)(fu->operand_1.integer.w + fu->operand_2.integer.w);
                result.integer.wu = (uint32_t) state->mem[addr]
                                  | ((uint32_t)state->mem[addr+1] <<  8)
                                  | ((uint32_t)state->mem[addr+2] << 16)
                                  | ((uint32_t)state->mem[addr+3] << 24);
                break;
            }
 
            case OPERATION_STORE: {
                uint32_t addr = (uint32_t)(fu->operand_1.integer.w + FIELD_IMM(instr));
                uint32_t val  = fu->operand_2.integer.wu;
                state->mem[addr]   =  val        & 0xFF;
                state->mem[addr+1] = (val >>  8) & 0xFF;
                state->mem[addr+2] = (val >> 16) & 0xFF;
                state->mem[addr+3] = (val >> 24) & 0xFF;
                break;
            }
 
            /* Jumps and branches.
             *
             * fu->insn_num = byte-address of this instruction (orig_pc).
             *
             * The assembler encodes:
             *   offset = target - (orig_pc + 4)
             * so the simulator must compute:
             *   target = orig_pc + 4 + offset                            */
            case OPERATION_J:    result.integer.w = 1; break;   /* taken */
            case OPERATION_JAL:  result.integer.w = 0; break;
            case OPERATION_JR:   result.integer.w = fu->operand_1.integer.w;     break;
            case OPERATION_JALR: result.integer.w = 0; break;
            case OPERATION_BEQZ: result.integer.w = (fu->operand_1.integer.w == 0) ? 1:0; break;
            case OPERATION_BNEZ: result.integer.w = (fu->operand_1.integer.w != 0) ? 1:0; break;
            default: result.integer.w = 0; break;
        }
 
        /* ---- Write-back ---- */
 
        if (op_info->fu_group_num == FU_GROUP_MEM && op_info->operation == OPERATION_LOAD) {
            int dest = (int)FIELD_R2(instr);
            if (state->reg_map_int[dest] == fu)
                state->rf_int.reg_int[dest] = result.integer;
            clear_map_int(state, dest, fu);
 
        } else if (op_info->fu_group_num == FU_GROUP_BRANCH) {
            unsigned long orig_pc = fu->insn_num;
            if (fu->id >= 0 && fu->id < MAX_TRACKED_FU)
                orig_pc = issue_pc[fu->id];
            switch (op_info->operation) {
                case OPERATION_J:
                    state->pc = orig_pc + 4 + (unsigned long)(long)(int)FIELD_OFFSET(instr);
                    {
                        unsigned long addr = (unsigned long)state->pc;
                        state->if_id.instr = (uint32_t) state->mem[addr]
                                           | ((uint32_t)state->mem[addr + 1] <<  8)
                                           | ((uint32_t)state->mem[addr + 2] << 16)
                                           | ((uint32_t)state->mem[addr + 3] << 24);
                        state->if_id.insn_num = state->pc;
                    }
                    break;
                case OPERATION_JAL: {
                    int link = 31;
                    state->rf_int.reg_int[link].w = (int32_t)(orig_pc + 4);
                    clear_map_int(state, link, fu);
                    state->pc = orig_pc + 4 + (unsigned long)(long)(int)FIELD_OFFSET(instr);
                    {
                        unsigned long addr = (unsigned long)state->pc;
                        state->if_id.instr = (uint32_t) state->mem[addr]
                                           | ((uint32_t)state->mem[addr + 1] <<  8)
                                           | ((uint32_t)state->mem[addr + 2] << 16)
                                           | ((uint32_t)state->mem[addr + 3] << 24);
                        state->if_id.insn_num = state->pc;
                    }
                    break;
                }
                case OPERATION_JR:
                    state->pc = (unsigned long)(uint32_t)result.integer.w;
                    {
                        unsigned long addr = (unsigned long)state->pc;
                        state->if_id.instr = (uint32_t) state->mem[addr]
                                           | ((uint32_t)state->mem[addr + 1] <<  8)
                                           | ((uint32_t)state->mem[addr + 2] << 16)
                                           | ((uint32_t)state->mem[addr + 3] << 24);
                        state->if_id.insn_num = state->pc;
                    }
                    break;
                case OPERATION_JALR: {
                    int rd = (int)FIELD_R3(instr);
                    state->rf_int.reg_int[rd].w = (int32_t)(orig_pc + 4);
                    clear_map_int(state, rd, fu);
                    state->pc = (unsigned long)(uint32_t)fu->operand_1.integer.wu;
                    {
                        unsigned long addr = (unsigned long)state->pc;
                        state->if_id.instr = (uint32_t) state->mem[addr]
                                           | ((uint32_t)state->mem[addr + 1] <<  8)
                                           | ((uint32_t)state->mem[addr + 2] << 16)
                                           | ((uint32_t)state->mem[addr + 3] << 24);
                        state->if_id.insn_num = state->pc;
                    }
                    break;
                }
                case OPERATION_BEQZ:
                case OPERATION_BNEZ:
                    if (result.integer.w) {
                        state->pc = orig_pc + 4 + (unsigned long)(long)(int)FIELD_IMM(instr);
                        {
                            unsigned long addr = (unsigned long)state->pc;
                            state->if_id.instr = (uint32_t) state->mem[addr]
                                               | ((uint32_t)state->mem[addr + 1] <<  8)
                                               | ((uint32_t)state->mem[addr + 2] << 16)
                                               | ((uint32_t)state->mem[addr + 3] << 24);
                            state->if_id.insn_num = state->pc;
                            state->pc += 4;
                        }
                    } else {
                        state->pc = orig_pc + 4;
                        {
                            unsigned long addr = (unsigned long)state->pc;
                            state->if_id.instr = (uint32_t) state->mem[addr]
                                            | ((uint32_t)state->mem[addr + 1] <<  8)
                                            | ((uint32_t)state->mem[addr + 2] << 16)
                                            | ((uint32_t)state->mem[addr + 3] << 24);
                            state->if_id.insn_num = state->pc;
                            state->pc += 4;
                        }
                    }
                    
                    break;
                default:
                    break;
            }
            state->fetch_lock = FALSE;
 
        } else if (op_info->operation != OPERATION_STORE) {
            int dest = use_imm ? (int)FIELD_R2(instr) : (int)FIELD_R3(instr);
            if (dest != 0) {                        /* integer R0 is read-only */
                if (state->reg_map_int[dest] == fu)
                    state->rf_int.reg_int[dest] = result.integer;
                clear_map_int(state, dest, fu);
            }
        }
 
        wake_dependents(state, fu, result);
        release_fu(fu);
        (*num_insn)++;
    }
 
    /* ==================================================================
     * Floating-point CDB
     * ================================================================== */
    if (state->cdb_fp != NULL) {
        fu_t *fu = state->cdb_fp;
        state->cdb_fp = NULL;
 
        int use_imm;
        const op_info_t *op_info = decode_instr(fu->instr, &use_imm);
        uint32_t instr = fu->instr;
 
        operand_t result;
        result.flt = 0.0f;
 
        if (op_info->fu_group_num == FU_GROUP_MEM) {
            if (op_info->operation == OPERATION_LOAD) {
                uint32_t addr = (uint32_t)(fu->operand_1.integer.w + fu->operand_2.integer.w);
                uint32_t raw  = (uint32_t) state->mem[addr]
                              | ((uint32_t)state->mem[addr+1] <<  8)
                              | ((uint32_t)state->mem[addr+2] << 16)
                              | ((uint32_t)state->mem[addr+3] << 24);
                result.flt = *(float *)&raw;
 
                int dest = (int)FIELD_R2(instr);
                if (state->reg_map_fp[dest] == fu)
                    state->rf_fp.reg_fp[dest] = result.flt;
                clear_map_fp(state, dest, fu);          /* reg >= 0: handles F0 */
 
            } else {
                /* S.S: pass the raw IEEE-754 bits of the float to memory. */
                uint32_t addr = (uint32_t)(fu->operand_1.integer.w + FIELD_IMM(instr));
                uint32_t val  = *(uint32_t *)&fu->operand_2.flt;
                state->mem[addr]   =  val        & 0xFF;
                state->mem[addr+1] = (val >>  8) & 0xFF;
                state->mem[addr+2] = (val >> 16) & 0xFF;
                state->mem[addr+3] = (val >> 24) & 0xFF;
            }
 
        } else {
            /* FP arithmetic */
            switch (op_info->operation) {
                case OPERATION_ADD:  result.flt = fu->operand_1.flt + fu->operand_2.flt; break;
                case OPERATION_SUB:  result.flt = fu->operand_1.flt - fu->operand_2.flt; break;
                case OPERATION_MULT: result.flt = fu->operand_1.flt * fu->operand_2.flt; break;
                case OPERATION_DIV:  result.flt = fu->operand_1.flt / fu->operand_2.flt; break;
                default:             result.flt = 0.0f; break;
            }
 
            int dest = (int)FIELD_R3(instr);
            if (state->reg_map_fp[dest] == fu)
                state->rf_fp.reg_fp[dest] = result.flt;
            clear_map_fp(state, dest, fu);              /* reg >= 0: handles F0 */
        }
 
        wake_dependents(state, fu, result);
        release_fu(fu);
        (*num_insn)++;
    }
 
    /* ==================================================================
     * Termination check
     * ================================================================== */
    if (state->halted &&
        fu_list_done(state->int_rs_list)     &&
        fu_list_done(state->fp_add_rs_list)  &&
        fu_list_done(state->fp_mult_rs_list) &&
        fu_list_done(state->fp_div_rs_list)  &&
        fu_list_done(state->mem_fu_list)) {
        state->finished = TRUE;
    }

    if (halt_pending &&
        fu_list_done(state->int_rs_list)     &&
        fu_list_done(state->fp_add_rs_list)  &&
        fu_list_done(state->fp_mult_rs_list) &&
        fu_list_done(state->fp_div_rs_list)  &&
        fu_list_done(state->mem_fu_list)) {
        state->halted = TRUE;
        state->finished = TRUE;
        halt_pending = 0;
    }
}