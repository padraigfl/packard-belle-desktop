import React from "react";
import { ProgramContext } from "../../contexts/programs";
import { WindowProgram, SelectBox, ButtonForm } from "packard-belle";
import Window from "../tools/Window";

const TaskManager = props => (
  <ProgramContext.Consumer>
    {context =>
      !context.taskManager ? (
        <Window {...props} resizable={false}>
          {rnd => (
            <WindowProgram
              className="TEST"
              onClose={context.toggleTaskManager}
              onRestore={rnd.restore}
              onMaximize={rnd.maximize}
              changingState={rnd.state.changingState}
            >
              {context.activePrograms.map(c => (
                <div>{c.title}</div>
              ))}
              <SelectBox
                options={context.activePrograms.map(c => ({
                  title: c.title,
                  value: c.key
                }))}
              />
              <ButtonForm>End Task</ButtonForm>
            </WindowProgram>
          )}
        </Window>
      ) : null
    }
  </ProgramContext.Consumer>
);

export default TaskManager;
