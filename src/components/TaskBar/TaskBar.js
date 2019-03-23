import React from "react";
import { TaskBar as TaskBarComponent } from "packard-belle";
import { ProgramContext } from "../../contexts/programs";

const TaskBar = () => (
  <ProgramContext.Consumer>
    {context => (
      <TaskBarComponent
        options={context.startMenu}
        openWindows={context.openOrder.map(p => {
          const { activePrograms } = context;
          const programIdx = activePrograms.findIndex(x => x.id === p);
          return {
            ...activePrograms[programIdx],
            isActive: programIdx === activePrograms.length - 1,
            onClick: () => context.moveToTop(activePrograms[programIdx])
          };
        })}
      />
    )}
  </ProgramContext.Consumer>
);

export default TaskBar;
