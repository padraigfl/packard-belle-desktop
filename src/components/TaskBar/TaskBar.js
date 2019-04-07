import React from "react";
import { TaskBar as TaskBarComponent } from "packard-belle";
import { ProgramContext } from "../../contexts/programs";

const TaskBar = () => (
  <ProgramContext.Consumer>
    {context => (
      <TaskBarComponent
        options={context.startMenu}
        quickLaunch={context.quickLaunch}
        openWindows={context.openOrder.map(p => {
          const { activePrograms } = context;
          const programIdx = activePrograms.findIndex(x => x.id === p);
          const isActive = p === context.activeId;
          const onClick = isActive ? context.onMinimize : context.moveToTop;
          const { title, icon } = activePrograms[programIdx];
          return {
            title,
            icon,
            isActive,
            onClick: () => onClick(p)
          };
        })}
      />
    )}
  </ProgramContext.Consumer>
);

export default TaskBar;
