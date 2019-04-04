import React from "react";
import { ExplorerView, ExplorerIcon } from "packard-belle";
import { ProgramContext } from "../../contexts/programs";

const DesktopView = () => (
  <ProgramContext.Consumer>
    {context => (
      <ExplorerView>
        {context.desktop.map(option => (
          <ExplorerIcon key={option.title} {...option} />
        ))}
      </ExplorerView>
    )}
  </ProgramContext.Consumer>
);

export default DesktopView;
