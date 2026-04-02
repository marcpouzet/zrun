(* The Zelus compiler, version 2024-dev
  (2026-03-13-17:53) *)
open Ztypes
type ('d, 'c, 'b, 'a) machine_220 =
{mutable init_203: 'd;
 mutable init_202: 'c; mutable m_199: 'b; mutable m_197: 'a}
type ('a) machine_218 = {mutable i_217: 'a}
type ('d, 'c, 'b, 'a) machine_215 =
{mutable init_201: 'd;
 mutable init_200: 'c; mutable m_195: 'b; mutable m_193: 'a}
let (f) =
      let f_86 =
          (fun (x_87) -> let y_89 = 1 in
                         (+) ((+) ((+) y_89 y_89) x_87) x_87) in
      f_86
let (f1) =
      let f1_92 =
          (fun (x_93) ->
            let x_103 = (+) 1 2 in
            let x_105 = (+) x_103 1 in
            let h_102 = x_105 in
            h_102) in
      f1_92
let (f3) =
      let f3_106 =
          (fun (x_107) ->
            let m_112 =
                (fun (v_113) -> let x_116 = (+) v_113 1 in
                                (+) x_116 2) in
            m_112 2) in
      f3_106
let (main1) = let main1_117 = (fun _ -> f3 1) in
              main1_117
let (my_pid) =
      let my_pid_127 =
          (fun (h_128) (p_131, i_130, d_129) ->
            let machine_215 = 
              let machine_215_alloc () =
                ();
                { init_201 = (false:bool);
                  init_200 = (false:bool);
                  m_195 = ((-1.):float); m_193 = ((-1.):float) } in
              let machine_215_reset self_214  =
                ((self_214.init_201 <- true; self_214.init_200 <- true):
                unit) in
              let machine_215_step self_214 (u_132) =
                ((self_214.init_201 <- false;
                  (let u_150 = ( *. ) p_131 u_132 in
                   let u_147 = ( *. ) d_129 u_132 in
                   let _pre_m_194 = self_214.m_195 in
                   self_214.m_195 <- u_147;
                   (let u_143 = ( *. ) i_130 u_132 in
                    let _pre_m_192 = self_214.m_193 in
                    let o_145 =
                        if self_214.init_200
                        then 0.
                        else (+.) _pre_m_192 (( *. ) h_128 u_143) in
                    self_214.init_200 <- false;
                    self_214.m_193 <- o_145;
                    (+.) ((+.) o_145
                               (if self_214.init_201
                                then 0.
                                else (/.) ((-.) u_147 _pre_m_194) h_128))
                         (( *. ) h_128 u_150)))):float) in
               Node { alloc = machine_215_alloc;
                      reset = machine_215_reset; step = machine_215_step;
                      assertions = [] } in machine_215) in my_pid_127
let (h) = let h_152 = 0.1 in
          h_152
let (p) = let p_153 = 0.1 in
          p_153
let (i) = let i_154 = 0.1 in
          i_154
let (d) = let d_155 = 0. in
          d_155
let (main2) =
      let main2_156 =
          let machine_218 =
            let Node { alloc = i_217_alloc; step = i_217_step;
                                            reset = i_217_reset } = (my_pid 
                                                                    h
                                                                    (p, i, d)) 
                                                                     in
            let machine_218_alloc () =
              ();{ i_217 = i_217_alloc () (* discrete *)  } in
            let machine_218_reset self_216  =
              (i_217_reset self_216.i_217 :unit) in
            let machine_218_step self_216 _ =
              ((let u_157 = 1. in
                let o_158 = i_217_step self_216.i_217 u_157 in
                o_158):float) in
             Node { alloc = machine_218_alloc;
                    reset = machine_218_reset; step = machine_218_step;
                    assertions = [] } in
          machine_218 in main2_156
let (controller) =
      let controller_159 =
          (fun (h_160) (p_163, i_162, d_161) ->
            let machine_220 = 
              let machine_220_alloc () =
                ();
                { init_203 = (false:bool);
                  init_202 = (false:bool);
                  m_199 = ((-1.):float); m_197 = ((-1.):float) } in
              let machine_220_reset self_219  =
                ((self_219.init_203 <- true; self_219.init_202 <- true):
                unit) in
              let machine_220_step self_219 (u_164) =
                ((self_219.init_203 <- false;
                  (let u_190 = ( *. ) p_163 u_164 in
                   let u_187 = ( *. ) d_161 u_164 in
                   let _pre_m_198 = self_219.m_199 in
                   self_219.m_199 <- u_187;
                   (let u_183 = ( *. ) i_162 u_164 in
                    let _pre_m_196 = self_219.m_197 in
                    let o_185 =
                        if self_219.init_202
                        then 0.
                        else (+.) _pre_m_196 (( *. ) h_160 u_183) in
                    self_219.init_202 <- false;
                    self_219.m_197 <- o_185;
                    (+.) ((+.) o_185
                               (if self_219.init_203
                                then 0.
                                else (/.) ((-.) u_187 _pre_m_198) h_160))
                         u_190))):float) in
               Node { alloc = machine_220_alloc;
                      reset = machine_220_reset; step = machine_220_step;
                      assertions = [] } in machine_220) in controller_159
