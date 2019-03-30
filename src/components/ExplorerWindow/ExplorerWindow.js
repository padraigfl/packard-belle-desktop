import React from "react";
import { WindowExplorer } from "packard-belle";
import Window from "../tools/Window";
import "./_styles.scss";

export const buildMenu = props => [
  {
    title: "File",
    options: [
      { title: "Open", isDisabled: true },
      { title: "Close", onClick: () => props.onClose(props) }
    ]
  },
  {
    title: "Help",
    options: [{ title: `About ${props.title}`, isDisabled: true }]
  }
];

const Explorer = props => (
  <Window
    {...props}
    initialHeight={props.initialHeight || 200}
    initialWidth={props.initialWidth || 200}
  >
    {rnd => (
      <WindowExplorer
        title={props.title}
        icon={props.icon}
        footer={[
          { text: "needs 100% width height" },
          { text: "overflow control" }
        ]}
        onClose={() => props.onClose(props)}
        onMinimize={() => {}}
        onRestore={rnd.restore}
        onMaximize={rnd.maximize}
        changingState={rnd.state.isDragging || rnd.state.isResizing}
        className={props.isActive && "Window--active"}
        menuOptions={buildMenu(props)}
      >
        Children
      </WindowExplorer>
    )}
  </Window>
);

export default Explorer;
